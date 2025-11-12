% Use this editor as a MiniZinc scratch book
%========================================================
% ENSEMBLES
%========================================================

set of int: IR = 1..11;                % Employés réguliers à temps plein
set of int: IP = 12..24;               % Employés occasionnels à temps plein  
set of int: IE = 25..86;               % Étudiants occasionnels à temps partiel
set of int: I = IR union IP union IE;  % Ensemble de tous les employés

set of int: IC = IR;                                 % Employés disposés à être chefs d'équipes
set of int: IN = 10..11 union 12..16 union 25..39;   % Employés disposés à travailler la nuit (2 réguliers, 5 occasionnels, 15 étudiants)
set of int: IW = I;                                  % Employés disposés à travailler la fin de semaine 

% Ensemble des jours sur le planning d'horizon
int: horizon = 14;
set of int: J = 1..horizon;

% Ensemble des lundis (j ≡ 1 mod 7)
set of int: JL = {j | j in J where j mod 7 == 1};

% Ensemble des fins de semaine (j ≡ 0 ou 6 mod 7)
set of int: JW = {j | j in J where j mod 7 == 0 \/ j mod 7 == 6};

% Ensembles des blocs de 15 minutes
set of int: H = 1..96;  

% Ensemble des quarts de travail
enum Q = {q0_8, q7_8, q8_8, q11_5_8, q12_8, q14_8, q16_8, q16_4};

% Heures de début pour chaque quart
array[Q] of float: debut = [
  0.0, 7.0, 8.0, 11.5, 12.0, 14.0, 16.0, 16.0
];
     
% Durées pour chaque quart (en heures)
array[Q] of float: duree = [
  8.0, 8.0, 8.0, 8.0, 8.0, 8.0, 8.0, 4.0
];

% Heures de fin pour chaque quart
array[Q] of float: fin = [debut[q] + duree[q] | q in Q];

% Ensembles des quarts par type
set of Q: QN = {q0_8};                               % Quarts de nuit
set of Q: QJ = {q7_8, q8_8, q11_5_8, q12_8, q14_8};  % Quarts de jour  
set of Q: QS = {q16_8, q16_4};                       % Quarts de soir

% Paires de quarts qui démarrent à moins de 2 heures d'intervalle      

array[Q] of set of Q: quarts_2h = 
    [ {r | r in Q where debut[r] - debut[q] <= 2.0} | q in Q ];
  
  % Paires de quarts séparés de moins de 16 heures  
array[J, Q, J, Q] of bool: F = 
    array4d(J, Q, J, Q, 
        [ debut[qp] + (jp - 1) * 24.0 < fin[q] + (j - 1) * 24.0 + 16.0
        | j in J, q in Q, jp in J, qp in Q ]);

% Paires de quarts consécutifs qui peuvent former un quart de 12 heures
array[J, Q, J, Q] of bool: A = 
    array4d(J, Q, J, Q,
        [ debut[qp] + (jp - 1) * 24.0 = fin[q] + (j - 1) * 24.0 
          /\ duree[q] + duree[qp] == 12.0
        | j in J, q in Q, jp in J, qp in Q ]);

% Triplets de quarts consécutifs dont la durée totale > 12 heures
array[J, Q, J, Q, J, Q] of bool: T = 
    array6d(J, Q, J, Q, J, Q,
        [ debut[qp] + (jp - 1) * 24.0 = fin[q] + (j - 1) * 24.0 
          /\ debut[qpp] + (jpp - 1) * 24.0 = fin[qp] + (jp - 1) * 24.0 
          /\ duree[q] + duree[qp] + duree[qpp] > 12.0
        | j in J, q in Q, jp in J, qp in Q, jpp in J, qpp in Q ]);

% Congés posés par les employés réguliers
array[IR] of set of J: C =
  [ if i == 4 then {1}
    elseif i == 7 then {5}
    else {} endif
  | i in IR ];

%========================================================
% PARAMÈTRES
%========================================================

array[I] of float: T_max = 
    [40.0 | i in IR] ++  % Réguliers: 48h/semaine
    [40.0 | i in IP] ++  % Occasionnels: 40h/semaine
    [20.0 | i in IE];    % Étudiants: 20h/semaine

int: k = 2;% Tolérance absolue sur la différence d'effectifs entre quarts proches

array[I] of int: c_barre = 
    [24 | i in IR] ++  % Réguliers: 24 quarts/mois
    [20 | i in IP] ++  % Occasionnels: 20 quarts/mois
    [10 | i in IE];    % Étudiants: 10 quarts/mois
    
%array[I, J] of var 0..h: m_ij;   % Jours travaillés depuis le dernier jour de repos de l'employé i Initialisé à 0

%array[I, J] of var 0..h: n_ij;% Jours travaillés la nuit quand non autorisé pour l'employé i

%array[Q] of float: d_q;%JSP si nécessaire? Durée (en heures) du quart q ∈ QUARTS

array[J] of int: a_j = 
  [6,6,6,6,6,8,8,
   6,6,6,6,6,8,8]; % Quarts non comblés par jour (6 pour la semaine, 8 pour le FDS)


% Explicit 2D array definition (14 rows × 8 columns)
/*array[J,Q] of int: r_jq = [|
%   q1  q2  q3  q4  q5  q6  q7  q8
     %semaine 1
     2,  18,  20,  15,  14,  11, 7, 11 |  % j1
     2,  18,  20,  15,  14,  11, 7, 11 |  % j2
     2,  18,  20,  15,  14,  11, 7, 11 |  % j3
     2,  18,  20,  15,  14,  11, 7, 11 |  % j4
     2,  18,  20,  15,  14,  11, 7, 11 |  % j5
     2,  18,  20,  15,  14,  11, 7, 11 |  % j6
     2,  18,  20,  15,  14,  11, 7, 11 |  % j7
     %semaine 2
     3,  21,  23,  18,  17,  14,  10,  14 |  % j8
     3,  21,  23,  18,  17,  14,  10,  14 |  % j9
     3,  21,  23,  18,  17,  14,  10,  14 |  % j10
     3,  21,  23,  18,  17,  14,  10,  14 |  % j11
     3,  21,  23,  18,  17,  14,  10,  14 |  % j12
     3,  21,  23,  18,  17,  14,  10,  14 |  % j13
     3,  21,  23,  18,  17,  14,  10,  14 |  % j14
|];
*/

%==================================
%les nouveaux paramètres:
%==================================

%taux de service d'un employé (nombre d'appels répondus par bloc de 15 min)
int: lmd = 2; %2 si on veut lmd comme entier

%estimation du nombre d'appels au jour j bloc h
%on suppose (pour l'instant) que la distribution est constante sur tous les jours
%on a les donnés par heure, on présume une distribution uniforme sur les quarts, basé sur donnés 5nov-2dec
array[H] of int: n_h = [
  % h1 (blocs 1-4)
  3,3,3,4,
  % h2 (blocs 5-8) 
  2,2,3,3,
  % h3 (blocs 9-12)
  2,2,2,3,
  % h4 (blocs 13-16)
  2,2,2,2,
  % h5 (blocs 17-20)
  2,2,2,2,
  % h6 (blocs 21-24)
  2,2,3,3,
  % h7 (blocs 25-28)
  4,5,5,5,
  % h8 (blocs 29-32)
  8,8,9,9,
  % h9 (blocs 33-36)
  56,56,57,57,
  % h10 (blocs 37-40)
  58,58,59,59,
  % h11 (blocs 41-44)
  55,55,55,56,
  % h12 (blocs 45-48)
  50,50,50,51,
  % h13 (blocs 49-52)
  45,45,45,46,
  % h14 (blocs 53-56)
  45,46,46,46,
  % h15 (blocs 57-60)
  43,44,44,44,
  % h16 (blocs 61-64)
  43,44,43,44,
  % h17 (blocs 65-68)
  11,11,12,12,
  % h18 (blocs 69-72)
  11,11,12,12,
  % h19 (blocs 73-76)
  44,44,44,44,
  % h20 (blocs 77-80)
  43,43,43,43,
  % h21 (blocs 81-84)
  9,10,10,10,
  % h22 (blocs 85-88)
  8,8,8,8,
  % h23 (blocs 89-92)
  7,6,6,6,
  % h24 (blocs 93-96)
  5,5,4,4
];


%paramètre a_jh si le bloc h et dans le quart q
array[1..8] of set of H: plages_quarts = [
  1..31,   % Quart 1 : blocs 1 à 31
  29..60,  % Quart 2 : blocs 29 à 60  
  33..64,  
  46..77,  
  49..80,  
  57..88,
  65..96,
  65..81
];

%a_hq si bloc h est dans quart q
array[H, Q] of int: a_hq = array2d(H, Q,
  [if hb in plages_quarts[enum2int(q)] then 1 else 0 endif 
   | hb in H, q in Q
  ]);



% Préférence de l'employé i pour le jour j et le quart q ∈ [1, 20]
array[I,J,Q] of int: p = array3d(I,J,Q,
  [ let {
      % Score jour vs weekend
      int: score_j =
        if i in IR \/ i in IP then
          if j in (J diff JW) then 10 else 5 endif   % IR/IP : semaine > weekend
        else
          if j in JW then 10 else 5 endif            % IE : weekend > semaine
        endif;

      % Score quart (jour/soir/nuit)
      int: score_q =
        if i in IR \/ i in IP then       % IR/IP :
          if q in QJ then 10               % jour préféré
          elseif q in QS then 8            % soir toléré
          elseif i in IN then 5            % nuit neutre pour IN
          else 1                           % nuit détestée
          endif
        else                             % IE :
          if q in QS then 10               % soir préféré
          elseif q in QJ then 8            % jour toléré
          elseif i in IN then 5            % nuit tolérée pour IN
          else 2                           % nuit pas aimée
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

array[J, H] of var int: s_jh; %nombre d'employés présents le jours j

array[J,H] of var 0..1: z_jh;

%variable de linéarisation


%variable = 1 si personne i travail un quart de 12h au qart q et q+1 ou q et q-1, jour j 
%array[I, J, Q] of var 0..1: y_ijq;





%========================================================
% CONTRAINTES
%========================================================
%40 heures de travail granties pour employés reg
%constraint forall(i in IR, l in JL)(
%    sum(j in l..(l+6), q in Q)(
%        duree[q] * x_ijq[i,j,q]
%    ) >= 40.0
%);

/*
%ne depasse pas le temp max par employé
constraint forall(i in I, l in JL)(
    sum(j in l..(l+6), q in Q)(
        duree[q]*x_ijq[i,j,q]) <= T_max[i]
);
*/

%16h de repos sauf pour quarts de 12h
constraint forall(i in I, j in J, q in Q, jp in J, qp in Q where 
    F[j,q,jp,qp] /\ not A[j,q,jp,qp])(
    x_ijq[i,j,q] + x_ijq[i,jp,qp] <= 1
);
%contrainte sup pour eviter 8+4+8
constraint forall(i in I, j in J, q in Q, jp in J, qp in Q, jpp in J, qpp in Q where
    T[j,q,jp,qp,jpp,qpp])(
    x_ijq[i,j,q] + x_ijq[i,jp,qp]+x_ijq[i,jpp,qpp] <= 2
 );

%couverture 1
%constraint forall(j in J, q in Q)(
%    sum(i in I)(x_ijq[i,j,q]) >= r_jq[j,q]
%);

%couverture 2:
/*
constraint forall(j in J)(
    sum(q in Q, i in I)(x_ijq[i,j,q]) >= (sum(q in Q)(r_jq[j,q])+a_j[j])
);
*/

/*
%au moin 1 chef d'equipe
constraint forall(j in J)(
    sum(i in IC, q in QJ)(x_ijq[i,j,q]) >= 1
);

constraint forall(j in J)(
    sum(i in IC, q in QS)(x_ijq[i,j,q]) >= 1
);
*/

%un jour max de nuit travaillé non autorisé
constraint forall(i in I where not (i in IN))(
    sum(j in J, q in Q)(x_ijq[i,j,q]) <= 1
);
%np faire travail fin de semaine non consenti
 constraint forall(i in I where not (i in IW))(
    sum(j in J where not (j in JW), q in Q)(x_ijq[i,j,q]) = 0
 );
 
 % Contrainte des congés accordés
constraint forall(i in IR)(
    sum(j in C[i], q in Q)(x_ijq[i,j,q]) = 0
);
 

%contraintes ergonomiques
 constraint forall(i in I where not(i in IE), j in 2..horizon-1)(
    sum(q in QN)(x_ijq[i,j,q]) <= sum(q in QN)(x_ijq[i,j-1,q] + x_ijq[i,j+1,q])
 );
 
 constraint forall(i in I where not(i in IE), j in 2..horizon-1)(
    sum(q in QN)(x_ijq[i,j-1,q]+x_ijq[i,j,q]+x_ijq[i,j+1,q]) <= 2
 );
 
 %regrouper les congés isolés
% constraint forall(i in I where not(i in IE), j in J)(
%    sum(q in Q)(x_ijq[i,j-1,q] + x_ijq[i,j+1,q] - 2*x_ijq[i,j,q]) <= 1 +sum(q in Q)(x_ijq[i,j,q]*y_ijq[i,j,q])
%);
 
/*
 %contraintes qui initializent et mettes à jour les parametres m_ij, n_ij
 % Constraint to initialize m_i for day 1
constraint forall(i in I)(
    m_ij[i,1] = if sum(q in Q)(x_ijq[i,1,q]) > 0 then 1 else 0 endif
);

% Constraint to update m_i for subsequent days
constraint forall(i in I, j in 2..h)(
    m_ij[i,j] = if sum(q in Q)(x_ijq[i,j,q]) > 0 then 
                   m_ij[i,j-1] + 1 
                 else 
                   0 
                 endif
);

constraint forall(i in I, j in J)(
    m_ij[i,j] <= 5
);
 
 % Initialize n_i for day 1
constraint forall(i in I where not (i in IN))(
    n_ij[i,1] = if sum(q in QN)(x_ijq[i,1,q]) > 0 then 1 else 0 endif
);

% Update n_i for subsequent days for unauthorized employees
constraint forall(i in I where not (i in IN), j in 2..h)(
    n_ij[i,j] = if sum(q in QN)(x_ijq[i,j,q]) > 0 then 
                   n_ij[i,j-1] + 1 
                 else 
                   0 
                 endif
);

% Constraint: unauthorized employees can't work more than 2 nights in a row
constraint forall(i in I where not (i in IN), j in J)(
    n_ij[i,j] <= 2
);

*/

%=====+=+=+=
%Nouvelles contraintes
%=====+=+=+=

constraint forall(j in J, hb in H)(s_jh[j,hb] >=1) ;


constraint forall(j in J, hb in H)(
    s_jh[j,hb] = sum(i in I, q in Q)(a_hq[hb,q] * x_ijq[i,j,q])
);


int: M = 1000;
constraint forall(j in J, h in H)(
    n_h[h] <= 4 * lmd * s_jh[j,h] + M * z_jh[j,h]
);


%========================================================
% VARIABLES POUR LINÉARISATION
%========================================================

% Pour f2R, f2P, f2E
array[IR] of var float: diff_R;
array[IR] of var float: abs_diff_R;
array[IP] of var float: diff_P;  
array[IP] of var float: abs_diff_P;
array[IE] of var float: diff_E;
array[IE] of var float: abs_diff_E;

% Pour f3
var int: total_jour = sum(i in I, j in J, q in QJ)(x_ijq[i,j,q]);
var int: total_soir = sum(i in I, j in J, q in QS)(x_ijq[i,j,q]);
var int: diff_js = total_jour - total_soir;
var int: abs_diff_js;

% Pour f4  
array[I, J, Q, Q] of var 0..1: abs_diff_x;

%========================================================
% CONTRAINTES DE LINÉARISATION
%========================================================

% Linéarisation f2R, f2P, f2E
constraint forall(i in IR)(
    diff_R[i] = sum(j in J, q in Q)(x_ijq[i,j,q]) - c_barre[i] /\
    abs_diff_R[i] >= diff_R[i] /\
    abs_diff_R[i] >= -diff_R[i]
);

constraint forall(i in IP)(
    diff_P[i] = sum(j in J, q in Q)(x_ijq[i,j,q]) - c_barre[i] /\
    abs_diff_P[i] >= diff_P[i] /\
    abs_diff_P[i] >= -diff_P[i]
);

constraint forall(i in IE)(
    diff_E[i] = sum(j in J, q in Q)(x_ijq[i,j,q]) - c_barre[i] /\
    abs_diff_E[i] >= diff_E[i] /\
    abs_diff_E[i] >= -diff_E[i]
);

% Linéarisation f3
constraint abs_diff_js >= diff_js;
constraint abs_diff_js >= -diff_js;

% Linéarisation f4
constraint forall(i in I, j in J, q in Q, qp in quarts_2h[q])(
    abs_diff_x[i,j,q,qp] >= x_ijq[i,j,q] - x_ijq[i,j,qp] /\
    abs_diff_x[i,j,q,qp] >= x_ijq[i,j,qp] - x_ijq[i,j,q]
);

%========================================================
% FONCTIONS OBJECTIF LINÉARISÉES
%========================================================

% f1 reste linéaire
var float: f1 = sum(i in I, j in J, q in Q)(p[i,j,q] * x_ijq[i,j,q]);

% f2 linéarisées
var float: f2R = -sum(i in IR)(abs_diff_R[i]);
var float: f2P = -sum(i in IP)(abs_diff_P[i]);
var float: f2E = -sum(i in IE)(abs_diff_E[i]);

% f3 linéarisée (approximation)
var int: f3 = -abs_diff_js;

% f4 linéarisée
var float: f4 = -sum(i in I, j in J, q in Q, qp in quarts_2h[q])(abs_diff_x[i,j,q,qp]);

%f5:
var float: f5 = -sum(j in J, h in H)(z_jh[j,h]);

% Fonction objectif finale
array[1..6] of float: w = [1.0, 1.0, 1.0, 1.0, 1.0, 1.0];
var float: fo = 
    w[1] * f1 +
    w[2] * f2R + 
    w[3] * f2P +
    w[4] * f2E +
    w[5] * f3 +
    w[6] * f4; 

solve maximize fo;
 
