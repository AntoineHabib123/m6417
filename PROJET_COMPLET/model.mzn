include "data.dzn";

%========================================================
% DÉCLARATIONS (types seulement, valeurs dans data.dzn)
%========================================================

set of int: IR;                % Employés réguliers à temps plein
set of int: IP;                % Employés occasionnels à temps plein  
set of int: IE;                % Étudiants occasionnels à temps partiel
set of int: I;                 % Ensemble de tous les employés

set of int: IC;                % Employés disposés à être chefs d'équipes
set of int: IN;                % Employés disposés à travailler la nuit
set of int: IW;                % Employés disposés à travailler la fin de semaine 

int: horizon;
set of int: J;
set of int: W;

set of int: JL;
set of int: JW;

set of int: H;  

enum Q = {q0_8, q7_8, q8_8, q11_5_8, q12_8, q14_8, q16_8, q8_12};

array[Q] of int: debut_int;
array[Q] of int: duree_int;
array[Q] of int: fin_int;

set of Q: QN;
set of Q: QJ;
set of Q: QS;

% Congés
array[IR] of set of J: C;

% PARAMÈTRES
array[I] of float: T_max;
array[I] of int: c_barre;
int: patience;
int: lmd;
array[H] of int: n_h;
array[Q] of set of H: plages_quarts;
array[H, Q] of int: a_hq;
array[I,J,Q] of int: p;

%========================================================
% PRÉDICATS
%========================================================

% Use integer arithmetic for predicates
predicate is_F(int: j, Q: q, int: jp, Q: qp) =
    debut_int[qp] + (jp - 1) * 48 < fin_int[q] + (j - 1) * 48 + 32;

%========================================================
% VARIABLES DE DÉCISION
%========================================================

array[I, J, Q] of var 0..1: x_ijq;

array[J, H] of var int: s_jh;
array[J,H] of var 0..1: z_jh;

%========================================================
% CONTRAINTES ESSENTIELLES
%========================================================

constraint forall(i in I, j in J)(
    sum(q in Q)(x_ijq[i,j,q]) <= 1
);

constraint forall(i in IR, w in W)(
    sum(j in JL[w]..JL[w]+6, q in Q)(x_ijq[i,j,q]*duree_int[q]) >= 80
);

% Max night shifts
constraint forall(i in I where not (i in IN))(
    sum(j in J, q in QN)(x_ijq[i,j,q]) <= 1
);

% No weekend work if not allowed
constraint forall(i in I where not (i in IW))(
    sum(j in J where not (j in JW), q in Q)(x_ijq[i,j,q]) = 0
);

% Congés
constraint forall(i in IR)(
    sum(j in C[i], q in Q)(x_ijq[i,j,q]) = 0
);

/*
% Contraintes ergonomiques
constraint forall(i in I where not(i in IE), j in 2..horizon-1)(
     sum(q in QN)(x_ijq[i,j,q]) <= sum(q in QN)(x_ijq[i,j-1,q] + x_ijq[i,j+1,q])
);

constraint forall(i in I where not(i in IE), j in 2..horizon-1)(
     sum(q in QN)(x_ijq[i,j-1,q]+x_ijq[i,j,q]+x_ijq[i,j+1,q]) <= 2
);
*/

% Staffing calculation
constraint forall(j in J, hb in H)(
    s_jh[j,hb] = sum(i in I, q in Q)(a_hq[hb,q] * x_ijq[i,j,q])
);

constraint forall(j in J, h in H)(
    s_jh[j,h] >= 0 /\ s_jh[j,h] <= card(I)
);

% Coverage constraints
int: M = max(n_h);
constraint forall(j in J, h in H)(
    n_h[h] <= (patience+1) * lmd * s_jh[j,h] + M * z_jh[j,h]
);

% Contraintes de couverture minimales par type de quart
constraint forall(j in J)(
    sum(i in I, q in QN)(x_ijq[i,j,q]) >= 1
);

constraint forall(j in J)(
    sum(i in I, q in QJ)(x_ijq[i,j,q]) >= 1
);

constraint forall(j in J)(
    sum(i in I, q in QS)(x_ijq[i,j,q]) >= 1
);

%========================================================
% VARIABLES POUR LA CONTRAINTE DE REPOS DANS L'OBJECTIF
%========================================================

% Variable pour compter les violations de repos (pénalité douce)
% Version simplifiée : on pénalise si l'employé travaille jour j ET jour j+1

var int: violations_repos = sum(i in I, j in 1..horizon-1) (
     let {
         var 0..1: violation_jour =
            sum(q in Q)(x_ijq[i,j,q]) * sum(qp in Q)(x_ijq[i,j+1,qp])
     } in violation_jour
 );

%========================================================
% AUTRES COMPOSANTES DE L'OBJECTIF
%========================================================

int: M2 = 50;
var int: total_jour = sum(i in I, j in J, q in QJ)(x_ijq[i,j,q]);
var int: total_soir = sum(i in I, j in J, q in QS)(x_ijq[i,j,q]);
var int: diff_js = total_jour - total_soir;
var 0..M2: abs_diff_js;
constraint abs_diff_js >= diff_js; 
constraint abs_diff_js >= -diff_js;

% Overtime
int: M_OT_MAX = horizon * max([duree_int[q] | q in Q]); 
array[I] of var 0..M_OT_MAX: ot;
var 0..(card(I) * M_OT_MAX): total_ot = sum(i in I)(ot[i]);
constraint forall(i in I) (
    ot[i] >= sum(j in J, q in Q)(duree_int[q] * x_ijq[i,j,q]) - T_max[i] /\
    ot[i] >= 0
);

%========================================================
% OBJECTIF AVEC PÉNALITÉ POUR LES VIOLATIONS DE REPOS
%========================================================

% Score de préférence : correspondance employés ⇄ quarts ⇄ jours
var int: score_preferences =
    sum(i in I, j in J, q in Q)(p[i,j,q] * x_ijq[i,j,q]);

% Pénalité d’équilibre entre quarts de jour et du soir
var int: penalite_equilibre_jour_soir = -abs_diff_js;

% Pénalité : violations de la couverture (z_jh = 1)
var int: penalite_couverture =
    -sum(j in J, h in H)(z_jh[j,h]);

% Pénalité : heures supplémentaires totales
var int: penalite_heures_sup = - total_ot;

% Pénalité : violations des règles de repos
var int: penalite_repos = - violations_repos;


int: w_preferences;
int: w_equilibre_jour_soir;
int: w_couverture;
int: w_heures_sup;
int: w_repos;

var int: objectif =
      w_preferences            * score_preferences
    + w_equilibre_jour_soir    * penalite_equilibre_jour_soir
    + w_couverture             * penalite_couverture
    + w_heures_sup             * penalite_heures_sup
    + w_repos                  * penalite_repos;

solve maximize objectif;

%========================================================
% SORTIE JSON POUR ANALYSE PYTHON
%========================================================

output [
  "{\n",
  "  \"objectif\": ", show(objectif), ",\n",

  "  \"score_preferences\": ", show(score_preferences), ",\n",
  "  \"penalite_equilibre_jour_soir\": ", show(penalite_equilibre_jour_soir), ",\n",
  "  \"penalite_couverture\": ", show(penalite_couverture), ",\n",
  "  \"penalite_heures_sup\": ", show(penalite_heures_sup), ",\n",
  "  \"penalite_repos\": ", show(penalite_repos), ",\n",

  "  \"x_ijq\": ", show(x_ijq), ",\n",
  "  \"s_jh\": ", show(s_jh), ",\n",
  "  \"z_jh\": ", show(z_jh), "\n",
  "}\n"
];