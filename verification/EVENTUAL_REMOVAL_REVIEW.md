# Revue indépendante : non-domination et comparaison éventuelle

Date : 31 octobre 2026. Relecteur : agent `review_iii_routes`, distinct de
l'auteur des développements. Aucun Lean/Lake n'est lancé par cette revue.
Ce checkpoint approuve les interfaces A3 et A1–A2 avant leur usage substantiel ;
il ne certifie pas des preuves ou des compilations encore à venir. Mise à jour
explicite après le premier échange : le coordinateur a choisi $q=3/7$ et le
seuil $11/10$, à la place de $q=2/5$ et $21/20$, pour couvrir exactement le
seuil $1{,}1$ imprimé dans le texte. Les interfaces actives ci-dessous intègrent
ce choix, relu indépendamment et approuvé.

Source : `main.tex` 637–662 et les interfaces existantes de
`RemoveAttachMixture`, `RemoveAttachAnalytic`, `RRTUniformDepth`,
`RRTSplitIntegrals`. La route analytique a été examinée plus largement dans
`III_ROUTES_REVIEW.md`.

## A3 — PASS sur les cibles, avec la restriction n ≥ 1

Les cibles proposées sont les probabilités réelles des vraies lois :

$$
\Pr\big(H(\operatorname{removalShort}(n))=1\big)=\frac1{2n!},
\qquad
\Pr\big(H(\operatorname{removalLong}(n))=1\big)=\frac1{3(n+1)!},
\qquad n\geq1.
$$

L'orientation de la non-domination est exactement
`¬ Word.HeightLE (removalLong n) (removalShort n)`. La formule longue a la
plus petite probabilité en hauteur 1 et donc la plus grande queue au seuil 2.
Il ne faut pas inverser cet export en se fondant sur la comparaison des moyennes.

Les restrictions des deux formules à $n\geq1$ sont indispensables : à $n=0$,
la masse courte en hauteur 1 vaut **1**, et la masse longue vaut **1/2**.
Les valeurs affichées ci-dessus donneraient respectivement $1/2$ et $1/3$ et
seraient fausses. Le premier préfixe a une arête puis un gel ; le second a
deux arêtes puis un gel qui conserve la hauteur du RRT à deux arêtes.

### Route et première lecture du fichier auteur

`RemovalStarProbability.lean` a été lu dans sa version comportant les helpers
de CDF en hauteur 1 et le lemme
`RRTSplit.heightPairLaw_ae_not_both_zero`. Leur route est correcte :

- Dans la loi courte, la graine à profondeur zéro contribue avec poids $1/2$
  à la probabilité d'étoile du RRT à $n$ arêtes. La graine à profondeur un
  ne contribue plus dès $n\geq1$, puisque ce RRT a une hauteur strictement
  positive.
- Dans la loi longue, les profils de maximum mémorisé 2 ne contribuent pas
  en hauteur 1. Le profil $(0,1;M=1)$, de poids $1/3$, donne précisément la
  probabilité d'étoile du RRT à $n+1$ arêtes.
- Le profil $(1,1;M=1)$ ne contribue plus dès $n\geq1$ : les deux composantes
  ne peuvent pas avoir simultanément hauteur zéro quand leur somme d'arêtes
  est $n>0$. Le fichier déduit cette exclusion des vraies composantes et de
  leur validité, pas d'une nouvelle hypothèse de support.

Les exports finaux de masse en singleton et de non-domination nécessitent
aussi le passage des CDF aux singletons ou aux queues. En particulier, ne pas
identifier implicitement la CDF au seuil 1 à la masse du singleton sans exclure
la hauteur zéro. Le maximum initial 1 et sa conservation dans les lois des
graines fournissent cette exclusion. Les futurs exports complets restent à
relire avec leurs preuves effectives et leurs vérifications mécaniques.

### Lecture de l'implémentation A3 complète

La version complète de `RemovalStarProbability.lean` a ensuite été lue, avec
`removalShort_height_one`, `removalLong_height_one` et `removal_not_heightLE` :
**PASS sur les énoncés et la route effective**. Les vérifications mécaniques
actuelles restent celles du coordinateur ; cette revue n'a pas lancé Lean.

Le lemme général `Word.heightLaw_pos_of_attachments` prouve l'exclusion de la
hauteur zéro à partir de la vraie validité et du nombre de sommets, y compris
en cas d'extinction finale. Il est appliqué aux deux mots avec leurs
admissibilités déjà prouvées et leurs comptes d'attachements. Le passage des
CDF aux masses du singleton est donc justifié explicitement.

Les coefficients réels sont exactement $1/(2n!)$ et $1/(3(n+1)!)$, avec la
restriction $n\geq1$ conservée. La non-domination utilise les queues au seuil 2,
compléments des CDF au seuil 1, puis l'inégalité stricte des deux réciproques
factorielles positives. Son orientation est bien `¬ HeightLE long short`.
Ni la comparaison des espérances ni une hypothèse de couplage ne sont utilisées
comme prémisses. Cette implémentation couvre donc les assertions quantitatives
et la non-domination de III11 après les checks mécaniques et d'axiomes requis.

## A1 — PASS sur l'interface de moment négatif

La définition proposée

$$
u_n=\int s,\ (3/7)^{\operatorname{treeHeight}(s)}\,
  d\operatorname{treeLaw}(\texttt{allAttach},n)
$$

utilise la vraie loi du RRT à $n$ arêtes et une puissance naturelle d'un réel
positif. La cible

$$
\exists C>0\;\forall n\in\mathbb N,\qquad u_n\leq\frac C{n+1}
$$

est mathématiquement correcte. À $n=0$, on a $u_0=1$, donc le $C$ choisi
doit être au moins 1. Les petites tailles doivent être absorbées dans ce
même $C$, sans transformer sa dépendance en un choix par $n$.

La récurrence par première coupure et plus grande composante s'applique à
$n\geq1$, avec les composantes de tailles $k$ et $n-1-k$. Le regroupement est

$$
n u_n\leq\frac{10}{7}\sum_{j=\lfloor n/2\rfloor}^{n-1}u_j.
$$

Dans l'implémentation finale, l'égalité des tailles est attribuée à la
composante racine : le terme central du cas impair a donc le coefficient 1.
Il est bien majoré par $1+q$. Choisir la fille aurait donné le coefficient
$q$, également admissible, mais ce n'est pas le choix du code. Dans le cas
pair, chaque taille de la moitié supérieure a le coefficient $1+q$.
Le coefficient limite $(10/7)\log2<1$ autorise la récurrence forte de la route
déjà relue. Ce checkpoint n'ajoute aucune estimation négative de MGF comme
hypothèse d'un export du papier : l'estimation doit être prouvée ici.

## A2 — PASS sur les cibles de limites et leur interprétation

La queue inférieure proposée

$$
\Pr(H(R_n)\leq (11/10)\log n)\longrightarrow0
$$

est une conséquence correcte de A1, puisque
$(11/10)\log(7/3)<1$. Les conventions totalisées au petit indice $n=0$ ne
modifient pas une limite à l'infini. Le passage puissance/logarithme se fait
aux indices positifs.

La cible d'accroissement est

$$
\operatorname{meanHeight}(n+1)-\operatorname{meanHeight}(n)\longrightarrow0.
$$

Pour la relier à la probabilité de choisir un sommet maximal, il faut
échantillonner le parent uniforme **dans le même arbre** que sa hauteur
maximale. Le pont probabiliste doit être prouvé à partir de la vraie transition
conditionnelle. Il ne faut pas remplacer ce couple par deux variables
indépendantes. La borne de l'événement diagonal par les deux queues ne
nécessite ensuite aucune indépendance.

La limite précédente, la comparaison déjà prouvée dans `RemoveAttachMixture`
et, éventuellement, $n\geq2$ pour la correction factorielle, impliquent

$$
\forall^{\mathrm{éventuel}} n,\qquad
\mathbb E H(\operatorname{removalLong}(n))
<\mathbb E H(\operatorname{removalShort}(n)).
$$

Cette dernière cible est exactement la force de III10, et non seulement
l'existence de témoins arbitrairement grands déjà obtenue pour M1iii. L'identité
de probabilité et la limite des accroissements fournissent la force de III9.

### Modification approuvée : couvrir le seuil imprimé à 1,1 log n

Le premier choix $q=2/5$ avec puissance $1/(n+1)$ n'aurait fourni directement
que les seuils $c<1/\log(5/2)$, soit environ $c<1{,}091$. Il justifiait
$21/20$ mais pas littéralement la valeur $1{,}1$ de la source. Le choix a donc
été modifié avant implémentation pour couvrir cette valeur exacte.

Avec le choix actif $q=3/7$, le coefficient limite devient
$(10/7)\log2<1$ ; de plus
$\log(7/3)\leq\log2+1/6<13/15$, donc
$(11/10)\log(7/3)<143/150<1$. Les deux constantes sont donc compatibles
avec la récurrence de moment et le seuil exact de la source. La queue portant
sur $H_n\leq(11/10)\log n$ est même légèrement plus forte que nécessaire
pour la conclusion imprimée portant sur $H_n\geq1{,}1\log n$ avec probabilité
tendant vers un.

Même après A2, ni le centrage fin $e\log n-(3/2)\log\log n$, ni les queues
exponentielles centrées E1/E2 ne sont prouvés par cette route. Les couplages
d'arbres complets III1/I2 restent également distincts des lois de profils.

## Revue finale ciblée de l'implémentation A1–A2

Lecture complète, le 31 octobre 2026, de `HalfHarmonic.lean`,
`LargerComponentSum.lean`, `RRTNegativeMoment.lean`,
`RRTNegativeMomentBound.lean`, `RRTWeakLowerTail.lean`,
`RRTHeightIncrement.lean`, `RRTDeepestParent.lean` et
`RemovalEventually.lean`. Verdict : **PASS sur les énoncés et les routes
effectives**, avec les conditions et limites de portée ci-dessous.
Le coordinateur effectue la construction intégrée, l'audit d'axiomes et les
rejeux ; cette revue reste sans commande Lean/Lake.

### Groupement et récurrence forte

`sum_larger_component_le` attribue l'égalité des tailles à la gauche. La
réflexion des indices n'ajoute donc qu'une majoration du terme central, de
coefficient 1 à coefficient $1+q$. Le lemme est vrai aussi pour la somme vide
à zéro ; la récurrence de moments l'applique au RRT à $n+1$ arêtes, avec les
deux composantes de tailles $k$ et $n-k$.

`negativeMoment_succ_le` utilise la décomposition en hauteur sur les vraies
composantes de `pairLaw`, puis leur loi de mixture effectivement prouvée. Les
intégrabilités sont établies explicitement, les intégrales de chaque marginale
de produit sont identifiées aux moments correspondants, et la décroissance de
$q^h$ en $h$ est utilisée dans le bon sens. L'indépendance conditionnelle des
deux composantes provient de la loi E3, pas d'une nouvelle prémisse.

`HalfHarmonic` déduit les limites du quotient entier $\lfloor n/2\rfloor/n$
et de la fenêtre harmonique de la décomposition quotient/reste et de
`Real.tendsto_harmonic_sub_log`. La contraction porte exactement sur

$$
\frac{10}{7}\frac{n+1}{n}
\bigl(H_n^{\mathrm{harm}}-H_{\lfloor n/2\rfloor}^{\mathrm{harm}}\bigr)
\longrightarrow \frac{10}{7}\log2<1.
$$

Dans `negativeMoment_bound`, la constante choisie est $C=N+1$, où $N$ est
un seuil de contraction. Elle est strictement positive, couvre tous les
indices $n\leq N$ grâce à $u_n\leq1$, et couvre notamment $u_0=1$. Pour
$n>N$, les indices de `Finset.Ico (n/2) n` sont strictement inférieurs à
$n$ ; l'hypothèse de récurrence forte s'applique donc à chaque terme. Le
dénominateur $n$ est positif dans cette branche. Aucune dépendance illicite
de $C$ envers le $n$ de la conclusion ni aucune hypothèse de moment non prouvée
ne subsiste.

### Queue au seuil exact du manuscrit

`negativeRate` vaut bien $\log(7/3)$ et
`mgf_negativeRate_eq` relie la vraie MGF au moment naturel de base $3/7$ par
une identité point par point. La borne Markov porte sur le bon événement
inférieur, avec paramètre MGF négatif, et les intégrabilités viennent du
vrai modèle. Le remplacement de $C/(n+1)$ par $C/n$ est fait seulement pour
$n\geq1$.

`height_lower_tail_tendsto_zero` conclut pour
$H(R_n)\leq(11/10)\log n$, avec la bonne loi de hauteur à $n$ arêtes.
L'exposant $1-(11/10)\log(7/3)$ est strictement positif ; les conventions de
division/logarithme à zéro ne sont pas utilisées dans cette majoration
éventuelle. Cette preuve certifie le seuil exact $1{,}1$ employé dans le texte.

### Accroissement et vrai couple profondeur/hauteur

`transition_mean_height` exprime l'accroissement conditionnel de hauteur par
l'indicatrice du parent maximal, pour chaque choix actif légal d'un état
valide. La fraîcheur du nouveau sommet et la borne de profondeur par le
maximum sont déduites de cet état. Le résultat est intégré sous le vrai
noyau de transition ; l'intégrale de `deepestFraction` est ainsi égale à
`meanHeight (n+1) - meanHeight n`.

`deepestFraction_le_split` est une inégalité d'indicatrices moyennées, pas
une factorisation de probabilités. Son intégration utilise la queue inférieure
de la hauteur et la queue supérieure de la vraie profondeur uniforme E5.
Les deux mesures portent sur le même indice $n$, au même seuil $11/10$.
La non-négativité de l'accroissement est également fournie par la fraction
positive, ce qui justifie le squeeze vers zéro.

Dans `RRTDeepestParent`, le noyau `depthHeightKernel s` échantillonne la
profondeur sous `Forward.activeHeightKernel s` et conserve comme seconde
coordonnée `Forward.treeHeight s`. Les deux coordonnées proviennent donc de
**la même** valeur d'état $s$, ensuite mélangée par `treeLaw allAttach n`.
Ce n'est pas un produit des deux lois marginales. L'égalité de la première
marginale à `uniformVertexDepthLaw` utilise le vrai noyau actif ; sous le RRT
pur celui-ci est bien uniforme sur tous les sommets, comme déjà prouvé.

`meanHeight_increment_eq_deepest_probability` applique l'identité intégrale
conditionnelle à l'indicatrice de la diagonale. La probabilité est bien celle
du parent maximal dans le même arbre échantillonné, et non celle de deux
échantillons indépendants. La totalisation du noyau sur un état sans actif
est inoffensive : ces états sont exclus presque sûrement par
`before_extinction` dans l'utilisation RRT.

### Comparaison éventuelle et lignes couvertes

`removal_reversal_eventually` combine la limite de tous les accroissements
avec celle de $1/(6(n+1)!)$. La somme devient strictement inférieure à $1/12$,
et la comparaison d'espérances déjà prouvée est appliquée aux indices
$n\geq1$. La conclusion est exactement
`∀ᶠ n in atTop, (removalLong n).expectedHeight < (removalShort n).expectedHeight`,
avec le bon sens d'inégalité.

Avec les preuves A3 relues plus haut, ces exports couvrent les conclusions
de **III9, III10 et III11**, sous les vérifications mécaniques actuelles du
coordinateur. La limite de profondeur utilisée est la version normalisée
corrigée E5/SF4 ; la phrase littérale sans normalisation ne devient pas vraie
par cette nouvelle preuve. Les estimations fortes E1/E2 et les couplages
d'arbres complets de III1/I2 ne sont toujours pas prouvés par ces résultats.
