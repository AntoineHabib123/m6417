% Use this editor as a MiniZinc scratch book
% Version avec contrainte de repos dans l'objectif

%========================================================
% ENSEMBLES
%========================================================

set of int: IR = 1..11;                % Employés réguliers à temps plein
set of int: IP = 12..24;               % Employés occasionnels à temps plein  
set of int: IE = 25..86;               % Étudiants occasionnels à temps partiel
set of int: I = IR union IP union IE;  % Ensemble de tous les employés

set of int: IC = IR;                                 % Employés disposés à être chefs d'équipes
set of int: IN = 10..11 union 12..16 union 25..39;   % Employés disposés à travailler la nuit
set of int: IW = I;                                  % Employés disposés à travailler la fin de semaine 

int: horizon = 14;
set of int: J = 1..horizon;
set of int: W = 1..(horizon div 7);

set of int: JL = {j | j in J where j mod 7 == 1};
set of int: JW = {j | j in J where j mod 7 == 0 \/ j mod 7 == 6};

set of int: H = 1..96;  

enum Q = {q0_8, q7_8, q8_8, q11_5_8, q12_8, q14_8, q16_8, q8_12};

% Convert time parameters to integers (multiply by 2 to avoid decimals)
array[Q] of int: debut_int = [ 0, 14, 16, 23, 24, 28, 32, 16 ];
array[Q] of int: duree_int = [ 16, 16, 16, 16, 16, 16, 16, 24 ];
array[Q] of int: fin_int = [debut_int[q] + duree_int[q] | q in Q];

set of Q: QN = {q0_8};
set of Q: QJ = {q7_8, q8_8, q11_5_8, q12_8, q14_8, q8_12};
set of Q: QS = {q16_8, q8_12};

% Use integer arithmetic for predicates
predicate is_F(int: j, Q: q, int: jp, Q: qp) =
    debut_int[qp] + (jp - 1) * 48 < fin_int[q] + (j - 1) * 48 + 32;

% Congés
array[IR] of set of J: C =
  [ if i == 4 then {1}
    elseif i == 7 then {5}
    else {} endif
  | i in IR ];

%========================================================
% PARAMÈTRES
%========================================================

array[I] of float: T_max = 
    [80.0 | i in IR] ++
    [80.0 | i in IP] ++
    [40.0 | i in IE];

array[I] of int: c_barre = 
    [24 | i in IR] ++
    [20 | i in IP] ++
    [10 | i in IE];

int: lmd = 2;

array[H] of int: n_h = [
  3,3,3,4, 2,2,3,3, 2,2,2,3, 2,2,2,2,
  2,2,2,2, 2,2,3,3, 4,5,5,5, 8,8,9,9,
  56,56,57,57, 58,58,59,59, 55,55,55,56,
  50,50,50,51, 45,45,45,46, 45,46,46,46,
  43,44,44,44, 43,44,43,44, 11,11,12,12,
  11,11,12,12, 44,44,44,44, 43,43,43,43,
  9,10,10,10, 8,8,8,8, 7,6,6,6, 5,5,4,4
];

% Plages de quarts ajustées
array[Q] of set of H: plages_quarts = [
  1..31, 29..60, 33..64, 46..77, 49..80, 57..88, 65..96, 65..81
];

array[H, Q] of int: a_hq = array2d(H, Q, [
  if h in plages_quarts[q] then 1 else 0 endif
  | h in H, q in Q
]);

array[I,J,Q] of int: p = array3d(I,J,Q,
  [ let {
      int: score_j =
        if i in IR \/ i in IP then
          if j in (J diff JW) then 10 else 5 endif
        else
          if j in JW then 10 else 5 endif
        endif;

      int: score_q =
        if i in IR \/ i in IP then
          if q in QJ then 10
          elseif q in QS then 8
          elseif i in IN then 5
          else 1
          endif
        else
          if q in QS then 10
          elseif q in QJ then 8
          elseif i in IN then 5
          else 2
          endif
        endif;
    }
    in score_j + score_q
  | i in I, j in J, q in Q ]
);

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

%Max night shifts
constraint forall(i in I where not (i in IN))(
    sum(j in J, q in QN)(x_ijq[i,j,q]) <= 1
);

%No weekend work if not allowed
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
    n_h[h] <= 4 * lmd * s_jh[j,h] + M * z_jh[j,h]
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

% Calcul des violations de repos - version optimisée
/*
var int: violations_repos;

constraint violations_repos = sum(i in I, j in J, q in Q, jp in max(1,j-1)..min(horizon,j+1), 
    qp in Q where jp != j \/ qp != q) (
    if is_F(j,q,jp,qp) then x_ijq[i,j,q] * x_ijq[i,jp,qp] else 0 endif
);
*/

% Alternative: version encore plus simplifiée pour éviter la complexité
 var int: violations_repos = sum(i in I, j in 1..horizon-1) (
     let {
         var 0..1: violation_jour = sum(q in Q)(x_ijq[i,j,q]) * sum(qp in Q)(x_ijq[i,j+1,qp])
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
% OBJECTIVE AVEC PÉNALITÉ POUR LES VIOLATIONS DE REPOS
%========================================================

var int: f1 = sum(i in I, j in J, q in Q)(p[i,j,q] * x_ijq[i,j,q]);
var int: f3 = -abs_diff_js;
var int: f5 = -sum(j in J, h in H)(z_jh[j,h]);
var int: f_ot = - total_ot;
var int: f_repos = -violations_repos;

% Poids ajustés - forte pénalité pour les violations de repos
array[1..7] of int: a = [200, 1, 1, 1, 500, 1000, 2000]; 
var int: fo = a[1]*f1 + a[3]*f3 + a[5]*f5 + a[6]*f_ot + a[7]*f_repos;

solve maximize fo;

output [
  "Solution found!\n",
  "Objective: ", show(fo), "\n",
  "f1 (préférences): ", show(f1), "\n", 
  "f3 (équilibre jour/soir): ", show(f3), "\n", 
  "f5 (violations couverture): ", show(f5), "\n",
  "f_ot (overtime): ", show(total_ot), "\n",
  "f_repos (violations repos): ", show(violations_repos), "\n",
  "Coverage violations: ", show(sum(j in J, h in H)(z_jh[j,h])), "\n",
  "Total assignments: ", show(sum(i in I, j in J, q in Q)(x_ijq[i,j,q])), "\n", 
   "x_ijq: ", show(x_ijq) , "\n"
];
