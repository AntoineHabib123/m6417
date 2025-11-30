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

enum Q;

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

array[H] of float: n_h_sem;
array[H] of float: n_h_fds;
array[J,H] of float: n_jh =
  array2d(J,H, [ (if j in JW then n_h_fds[h] else n_h_sem[h] endif) | j in J, h in H ]);

array[Q] of set of H: plages_quarts;
array[H, Q] of int: a_hq;
array[I,J,Q] of int: p;


% Paires interdites
int: NB_PAIRES_INTERDITES;
array[1..NB_PAIRES_INTERDITES] of Q:   PI_q;
array[1..NB_PAIRES_INTERDITES] of Q:   PI_qp;



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

array[J, H] of var 0..card(I): s_jh;
array[J, H] of var int: z_jh; % demande insatisfaite (en min)

%========================================================
% CONTRAINTES ESSENTIELLES
%========================================================

% Domaine z_jh
constraint forall(j in J, h in H)(0 <= z_jh[j,h]);
constraint forall(j in J, h in H)(z_jh[j,h] <= max(n_jh));

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


% Contraintes ergonomiques
constraint forall(i in IN, j in 2..horizon-1)(
     sum(q in QN)(x_ijq[i,j,q]) <= sum(q in QN)(x_ijq[i,j-1,q] + x_ijq[i,j+1,q])
);

constraint forall(i in IN, j in 2..horizon-1)(
     sum(q in QN)(x_ijq[i,j-1,q]+x_ijq[i,j,q]+x_ijq[i,j+1,q]) <= 2
);


% Staffing calculation
constraint forall(j in J, hb in H)(
    s_jh[j,hb] = sum(i in I, q in Q)(a_hq[hb,q] * x_ijq[i,j,q])
);

constraint forall(j in J, h in H)(
    s_jh[j,h] >= 0 /\ s_jh[j,h] <= card(I)
);

% Coverage constraints
constraint forall(j in J, h in H)(
    n_jh[j,h] <= lmd * s_jh[j,h] + z_jh[j,h]
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

% 16h repos
constraint forall(i in IR union IP, j in 1..horizon-1, k in 1..NB_PAIRES_INTERDITES)(
    x_ijq[i, j, PI_q[k]]  +  x_ijq[i, j+1, PI_qp[k]] <= 1
);

% Max 1 quart par jour
constraint forall(i in I, j in J)(
    sum(q in Q)(x_ijq[i,j,q]) <= 1
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

%========================================================
% OBJECTIF AVEC PÉNALITÉ POUR LES VIOLATIONS DE REPOS
%========================================================

% Score de préférence : correspondance employés ⇄ quarts ⇄ jours
var int: score_preferences =
    sum(i in I, j in J, q in Q)(p[i,j,q] * x_ijq[i,j,q]);

% Pénalité d’équilibre entre quarts de jour et du soir
var int: penalite_equilibre_jour_soir = -abs_diff_js;

% Pénalité : violations de la couverture (nombre de minutes non servies)
var int: max_z;
constraint forall(j in J, h in H)(max_z >= z_jh[j,h]);

var int: penalite_couverture =
    -max_z;

% Pénalité : heures supplémentaires totales
var int: penalite_heures_tot = - sum(i in I, j in J, q in Q)((duree_int[q] div 2)*x_ijq[i,j,q]);


int: w_preferences;
int: w_equilibre_jour_soir;
int: w_couverture;
int: w_heures_tot;

var int: objectif =
      w_preferences            * score_preferences
    + w_equilibre_jour_soir    * penalite_equilibre_jour_soir
    + w_couverture             * penalite_couverture
    + w_heures_tot             * penalite_heures_tot;

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
  "  \"penalite_heures_tot\": ", show(penalite_heures_tot), ",\n",

  "  \"x_ijq\": ", show(x_ijq), ",\n",
  "  \"s_jh\": ", show(s_jh), ",\n",
  "  \"z_jh\": ", show(z_jh), "\n",
  "}\n"
];