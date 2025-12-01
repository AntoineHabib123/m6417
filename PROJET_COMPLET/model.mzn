include "data.dzn";

%========================================================
% DONNÉES
%========================================================

% ENSEMBLES
set of int: IR;
set of int: IP;
set of int: IE;
set of int: I;  

set of int: IC;
set of int: IN;
set of int: IW;

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

array[1..NB_PAIRES_INTERDITES] of Q:   PI_q;
array[1..NB_PAIRES_INTERDITES] of Q:   PI_qp;

array[IR] of set of J: C;

% PARAMÈTRES
int: horizon;

array[I] of float: T_max;
int: lmd;

array[H] of float: n_h_sem;
array[H] of float: n_h_fds;
array[J,H] of float: n_jh =
  array2d(J,H, [ (if j in JW then n_h_fds[h] else n_h_sem[h] endif) | j in J, h in H ]);

array[Q] of set of H: plages_quarts;
array[Q] of set of H: plages_pause_15;
array[Q] of set of H: plages_pause_60;

array[H, Q] of float: a_hq;
array[I,J,Q] of int: p;

int: NB_PAIRES_INTERDITES;

int: w_preferences;
int: w_couverture;
int: w_heures_tot;

%========================================================
% VARIABLES DE DÉCISION
%========================================================

% x_ijq[i,j,q] = 1 si l'employé i assigné au jour j, quart q
array[I, J, Q] of var 0..1: x_ijq;

% Nombre d'employés présents le jour j au bloc h (pondéré par taux de présence)
array[J, H] of var float: s_jh;

% Demande non satisfaite (en min)
array[J, H] of var int: z_jh;
var int: max_z;


%========================================================
% CONTRAINTES ESSENTIELLES
%========================================================

% Max 1 quart par jour
constraint forall(i in I, j in J)(
    sum(q in Q)(x_ijq[i,j,q]) <= 1
);

% 40 heures garanties pour IR
constraint forall(i in IR, w in W)(
    sum(j in JL[w]..JL[w]+6, q in Q)(x_ijq[i,j,q]*duree_int[q]) >= 80
);

% Temps de travail max autorisé
constraint forall(i in IR, w in W)(
    sum(j in JL[w]..JL[w]+6, q in Q)(x_ijq[i,j,q]*duree_int[q]) <= T_max[i]
);

% Pas de quart de nuit si l'employé ne peut pas
constraint forall(i in (I diff IN), j in J, q in QN)(
    x_ijq[i,j,q] = 0
);

% Pas de fin de semaine si l'employé ne peut pas
constraint forall(i in (I diff IW), j in (J diff JW), q in Q)(
    x_ijq[i,j,q] = 0
);

% Jours de congé pour IR
constraint forall(i in IR, j in C[i], q in Q)(
    x_ijq[i,j,q] = 0
);

% Pas de nuits isolées
constraint forall(i in IN, j in 2..horizon-1)(
     sum(q in QN)(x_ijq[i,j,q]) <= sum(q in QN)(x_ijq[i,j-1,q] + x_ijq[i,j+1,q])
);

% Pas 3 nuits consécutives
constraint forall(i in IN, j in 2..horizon-1)(
     sum(q in QN)(x_ijq[i,j-1,q]+x_ijq[i,j,q]+x_ijq[i,j+1,q]) <= 2
);

% Définition de s_jh
constraint forall(j in J, hb in H)(
    s_jh[j,hb] = sum(i in I, q in Q)(a_hq[hb,q] * x_ijq[i,j,q])
);

% Définition de n_jh
constraint forall(j in J, h in H)(
    n_jh[j,h] <= lmd * s_jh[j,h] + z_jh[j,h]
);

% Au moins un employé présent par nuit / jour / soir chaque jour
constraint forall(j in J)(
    sum(i in I, q in QN)(x_ijq[i,j,q]) >= 1
);
constraint forall(j in J)(
    sum(i in I, q in QJ)(x_ijq[i,j,q]) >= 1
);
constraint forall(j in J)(
    sum(i in I, q in QS)(x_ijq[i,j,q]) >= 1
);

% 16h de repos entre chaque quart
constraint forall(i in IR union IP, j in 1..horizon-1, k in 1..NB_PAIRES_INTERDITES)(
    x_ijq[i, j, PI_q[k]]  +  x_ijq[i, j+1, PI_qp[k]] <= 1
);

% Définition de max_z
constraint forall(j in J, h in H)(
    max_z >= z_jh[j,h]
);


% Domaine z_jh
constraint forall(j in J, h in H)(
    0 <= z_jh[j,h]
);
constraint forall(j in J, h in H)(
    z_jh[j,h] <= max(n_jh)
);

% Domaine de s_jh
constraint forall(j in J, h in H)(
    s_jh[j,h] >= 0 /\ s_jh[j,h] <= card(I)
);

%========================================================
% OBJECTIF
%========================================================

% Score de préférence
var int: score_preferences =
    sum(i in I, j in J, q in Q)(p[i,j,q] * x_ijq[i,j,q]);

% Pénalité : violations de la couverture (max demande non satisfaite)
var int: penalite_couverture = -max_z;

% Pénalité : heures prestées totales
var int: penalite_heures_tot = - sum(i in I, j in J, q in Q)((duree_int[q] div 2)*x_ijq[i,j,q]);

var int: objectif =
      w_preferences            * score_preferences
    + w_couverture             * penalite_couverture
    + w_heures_tot             * penalite_heures_tot;

solve maximize objectif;

%========================================================
% SORTIE JSON
%========================================================

output [
  "{\n",
  "  \"objectif\": ", show(objectif), ",\n",

  "  \"score_preferences\": ", show(score_preferences), ",\n",
  "  \"penalite_couverture\": ", show(penalite_couverture), ",\n",
  "  \"penalite_heures_tot\": ", show(penalite_heures_tot), ",\n",

  "  \"x_ijq\": ", show(x_ijq), ",\n",
  "  \"s_jh\": ", show(s_jh), ",\n",
  "  \"z_jh\": ", show(z_jh), "\n",
  "}\n"
];