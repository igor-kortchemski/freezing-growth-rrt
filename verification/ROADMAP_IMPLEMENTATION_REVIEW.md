# Revue indépendante des interfaces et de l'implémentation de la roadmap

Date : 31 octobre 2026. Relecteur : agent `review_iii_routes`, distinct de
l'auteur des fichiers. Aucun Lean/Lake n'a été lancé par cette revue. Les
compilations P1/P2 sont rapportées par le coordinateur ; elles ne deviennent
pas des vérifications indépendantes du noyau du fait de cette lecture.

Périmètre lu : `main.tex` 635–649 et les passages du split/greffe déjà examinés
dans `III_ROUTES_REVIEW.md` ; `RRTMeanUpper.lean`, `RRTSplitSymmetry.lean`,
`RRTSplitLaw.lean`, `RRTSplitKernel.lean`, `RRTSplitMixture.lean`, et
`HeightProfile.lean`. Les verdicts P3 ci-dessous portent sur les interfaces
proposées avant leur utilisation substantielle, et non sur une preuve Lean
encore à écrire.

## P1 — PASS sur l'interface et la route lue

Les exports de `FreezingGrowth.RRT` conservent la vraie loi du RRT à $n$
arêtes :

- `meanHeight n` est l'intégrale de `Forward.treeHeight` sous
  `Forward.treeLaw allAttach n`.
- `meanHeight_eq_word` utilise le mot pur de longueur $n$, via le pont effectif
  `replicate_heightLaw`, et non une identification supposée des deux modèles.
- `meanHeight_le` a le majorant
  $\log(n+1)+1+(\exp1-1)\operatorname{heightScale}(\texttt{allAttach},n)$,
  obtenu par Jensen et la borne MGF existante. Le majorant vaut 1 à $n=0$ ;
  la borne est donc valable dès zéro sans modifier la cible.
- `meanHeight_div_tendsto_zero` concerne une limite à l'infini. La division
  totalisée à zéro et les petits indices ne changent pas cette limite.
- `meanHeight_exists_small_increment` donne, pour tout $\varepsilon>0$ et
  tout $N$, un $n\geq N$ avec un accroissement inférieur à $\varepsilon$.
  Il ne conclut pas à la convergence de tous les accroissements.

La route lue dans `RRTMeanUpper.lean` fournit ses intégrabilités et ses bornes
affines. Elle n'introduit ni E1/E2, ni E5, ni une hypothèse asymptotique dans
un résultat du papier. P1 est une étape suffisante pour l'existence de M1iii
après P4/P5 ; il ne ferme pas III9/III10.

## P2 — PASS ; E3 et III6 sont couverts par les exports

La définition `RRTSplit.pairLaw n` est directement le pushforward de
`Forward.treeLaw allAttach (n+1)` par la paire des vraies composantes de
`firstEdgeSplit`. Ce n'est pas une nouvelle loi auxiliaire à laquelle on
attribuerait la bonne interprétation par hypothèse.

`pairLaw_eq_sum` est obtenu du théorème de loi jointe effectif. `pairLaw_swap`
utilise `Measure.prod_swap` et la réflexion $k\mapsto n-k$ de la somme.
Le tag de taille est oublié avant le swap : aucune égalité conditionnelle
fausse entre les deux tailles n'est revendiquée. Le code traite la mesurabilité
produit avec les projections/swap et non avec une hypothèse arbitraire de
mesurabilité depuis l'espace produit.

`heightPairLaw` est le pushforward de cette paire par les vraies hauteurs,
avec `measurable_heightPair` explicite. L'invariance de cette loi implique
que les événements $A=B+1$ et $B=A+1$ sont équiprobables. Ils sont disjoints,
et leur union a une masse au plus un. Le théorème
`heightPairLaw_tie_le_half` a donc exactement la borne réelle $1/2$ nécessaire
à III6.

Le paramètre $n\geq0$ représente le RRT à $n+1$ arêtes. À $n=0$, les deux
composantes sont des singletons ; l'événement d'égalité décalée est vide.
Cette borne n'ajoute aucune hypothèse de survie ou d'indépendance.

Avec la loi jointe et les ponts de composantes déjà prouvés, ces nouveaux
exports couvrent l'échangeabilité auparavant manquante à E3 et la borne de
III6. Les statuts de complétion restent à accompagner des types, compilations
et clôtures d'axiomes actuels du coordinateur au jalon d'intégration.

## P3 — PASS sur les interfaces proposées

Les définitions proposées sont sur le profil existant, avec $a,b,M\in\mathbb N$ :

$$
\operatorname{shift}_{a,M}(p)
=\bigl(\operatorname{map}(a+\cdot)\,p.\mathrm{activeDepths},
        \max(M,a+p.\mathrm{maximum})\bigr),
$$

$$
\operatorname{join}_{a,b,M}(p,q)
=\bigl(\operatorname{map}(a+\cdot)\,p.\mathrm{activeDepths}
       +\operatorname{map}(b+\cdot)\,q.\mathrm{activeDepths},
       \max(M,\max(a+p.\mathrm{maximum},b+q.\mathrm{maximum}))\bigr).
$$

`grow p n` part de la masse de Dirac en $p$ puis applique $n$ fois le vrai
`HeightProfile.transitionLaw _ true`.

La cible à une graine est fidèle : sous $a\leq M$,

$$
\operatorname{grow}(\{a\},M,n)
=\operatorname{map}\bigl(s\mapsto
  \operatorname{shift}_{a,M}(\operatorname{ofState}(s))\bigr)
  (\operatorname{treeLaw}(\texttt{allAttach},n)).
$$

La cible à deux graines est fidèle : sous $\max(a,b)\leq M$,

$$
\operatorname{grow}(\{a,b\},M,n)
=\operatorname{map}\bigl(r\mapsto
  \operatorname{join}_{a,b,M}
  (\operatorname{ofState}(r.2.1),\operatorname{ofState}(r.2.2))\bigr)
  (\operatorname{mixtureLaw}(n)).
$$

Les accolades ci-dessus désignent des **multisets**, pas des finsets. Si
$a=b$, il reste deux occurrences initiales et deux choix. Après $n$ ajouts,
le nombre d'actifs est $n+2$ dans la cible à deux graines ; les composantes
de la mixture ont respectivement $k+1$ et $n-k+1$ sommets. Il n'y a pas
d'arête supplémentaire à ajouter entre les deux graines dans ce profil.

Les conditions sur $M$ sont les bonnes conditions initiales et sont nécessaires
dès $n=0$ : le maximum de l'image initiale doit être $M$. Elles ne cachent pas
une estimation probabiliste à établir plus tard. Le maximum $M$ reste présent
même quand il est strictement supérieur aux profondeurs des graines ; les
hauts sommets gelés ne disparaissent donc pas.

La cible est un peu plus générale que les profils physiquement réalisés par
un arbre connexe à racine unique, ce qui est permis pour un helper : la
dynamique de profils est définie sur tous ces profils. Ses applications au
papier doivent partir des profils effectivement projetés des petits préfixes.

### Point important pour la preuve d'entrelacement

Il ne faut pas énoncer la commutation du noyau `RRTSplit.growthKernel n` avec
`join` pour tout `Result` arbitraire. Les poids de ce noyau dépendent du tag
de taille : si le tag ne correspond pas aux cardinalités actives des deux
états, ils ne représentent pas un choix uniforme dans leur union.

L'auxiliaire correct se prouve sur le support réel de `mixtureLaw n`, ou
sous `componentLaw k (n-k)` avec $k\leq n$. Ce support fournit la validité
des deux états locaux, les fraîcheurs des identifiants locaux, et les
cardinalités $k+1$, $n-k+1$. Ces faits doivent être déduits des lois RRT
existantes ; aucune de ces prémisses ne doit rester dans la cible finale.

Sur ce support, les identités déterministes de `join` avec une insertion
dans la première ou la seconde composante sont correctes : l'insertion globale
est à profondeur $a+d+1$ ou $b+d+1$, le maximum se met à jour par un maximum,
et les autres occurrences restent inchangées. La loi uniforme sur la somme
des multisets est la mixture des deux lois uniformes avec leurs poids de
cardinalités. Cela fournit exactement les coefficients de `growthKernel`.

Pour la cible à une graine, `shift` commute avec l'ajout de profondeur $d+1$
en la transformant en l'ajout de profondeur $(a+d)+1$. Une preuve de cette
commutation pour le noyau de profils, puis une induction, évite une nouvelle
construction de graphes.

La mesurabilité des applications sur les produits de deux états doit rester
explicite, comme dans P2. `Forward.State × Forward.State` porte l'espace
mesurable produit ; ne pas lui attribuer implicitement l'espace total.

## Portée après P3

Ces égalités de lois de profils/hauteurs sont suffisantes pour P4 et M1iii.
Elles ne certifient pas automatiquement III1/I2 comme couplages d'arbres
complets avec toutes leurs étiquettes. Il faudra conserver cette distinction
dans le rapport même après une preuve complète de M1iii.

## Revue finale ciblée de l'implémentation P3–P5

Verdict du 31 octobre 2026 : **PASS pour les énoncés et la route de preuve
effectivement lus**. Le coordinateur rapporte la compilation P3/P4 et réalise
la compilation P5, la construction intégrée, l'audit d'axiomes et les rejeux
séparément. Aucun Lean/Lake n'a été lancé par cette revue ; les verdicts ne
remplacent pas ces vérifications mécaniques actuelles.

Lecture complémentaire complète : `SeededHeightGrowth.lean`,
`SeededHeightLaw.lean`, `SeededWordLaw.lean`, `RRTSplitIntegrals.lean`,
`SeededHeightExpectation.lean`, `RemoveAttachMixture.lean` et
`RemoveAttachAnalytic.lean`, confrontés à `main.tex` 554–649 et à
`FreezingGrowth.RemoveAttachClaim` dans `MainStatements.lean`.

### P3 implémenté : vrais noyaux et absence de prémisses orphelines

`shift_attach`, `join_attach_left` et `join_attach_right` conservent le maximum
antérieur et les anciennes profondeurs. `ofMultiset_add` décompose la loi
uniforme sur les **occurrences** avec les bonnes proportions de cardinalités.
Les hypothèses de positivité du lemme technique `join_transition` sont ensuite
fournies par les vrais états RRT ; elles ne restent pas dans les théorèmes
finaux.

`single_seed_growth` ne suppose que $a\leq M$, et `join_seed_growth` seulement
$\max(a,b)\leq M$, comme aux interfaces relues. Le lemme intermédiaire
`map_sizeKernel_project` demande correctement validité et cardinalités locales.
Dans la récurrence finale, ces faits sont tirés de
`treeLaw_split_describes`, des cardinalités des composantes et de leur somme
d'arêtes. L'entrelacement n'est donc pas postulé pour des états arbitraires ou
pour un tag incohérent.

La mesurabilité du projecteur de deux états est justifiée via les projections
produit et la dénombrabilité de `HeightProfile`. Aucune identification illicite
de l'espace mesurable de `State × State` à l'espace total n'est utilisée.
Le cas de deux profondeurs égales demeure un multiset de cardinal deux.

### P4 implémenté : raccord aux vrais mots et espérances

`SeededWordLaw.wordLaw_append_replicate` établit l'évolution du suffixe à partir
de la vraie loi du préfixe. Les deux tables de deux/trois opérations sont
certifiées par `decide +kernel`, puis reliées à cette loi par
`ProfileEnumeration.run_normalized_law`. Leur usage ne suppose donc ni des
poids de configurations ni une indépendance envers le préfixe.

Les deux occurrences actives `{1,1}` sont conservées. Le profil `{0,1}` de
maximum 2 reste distinct de celui de maximum 1 : le sommet gelé haut ne
disparaît pas. Les poids de la loi longue sont bien $2/6,1/6,1/6,1/6,1/6$.

Les intégrabilités sont explicitement établies. En particulier,
`RRTSplit.heightPairLaw_integrable` utilise un support borné des **vraies**
composantes, puis `SeededHeightExpectation` transporte cette intégrabilité
aux lois des graines. Les manipulations d'intégrales ne reposent donc pas
sur la convention de valeur nulle d'une intégrale non intégrable.

`removalShort_expectedHeight` a la condition correcte $n\geq1$ ; à $n=0$,
l'égalité avec $a_0+1/2$ serait fausse. `removalLong_expectedHeight` est valable
pour tout $n\geq0$ et utilise la moyenne de référence $a_{n+1}$, la loi des
composantes indexée par `heightPairLaw n`, et la correction $1/(6(n+1)!)$.
Les réindexations $n$ versus $n+1$ concordent avec le nombre d'ajouts et le
bord supprimé dans la première coupure.

`heightMixture_eq_seeds` identifie les cinq profils au vrai intégrande du
manuscrit. `heightMixture_eq_height_add_corrections` fournit l'identité corrigée
SF1 ; le terme C erroné imprimé n'est pas validé pour autant.
`RRTSplit.integral_max_heightPairLaw`, `heightPairLaw_height_one` et
`heightPairLaw_tie_le_half` identifient la moyenne, l'événement d'étoile et la
borne de correction avec leurs vraies lois. On obtient bien
`removal_expectedHeight_comparison`, sans hypothèse de greffe ou de comparaison
restée ouverte.

### P5 implémenté : exactitude de la cible principale

`removalLong n` et `removalShort n` sont exactement les mots de
`RemoveAttachClaim`. Leur admissibilité est prouvée pour le $n$ variable, en
utilisant la positivité terminale de leurs petits préfixes, et non reprise
seulement du témoin fixe 13.

`removal_reversal_arbitrarily_late N` choisit un petit accroissement après
$\max(N,2)$. Les bornes fournies sont bien $\delta_n<1/24$ et
$1/(6(n+1)!)\leq1/36$, d'où un écart long moins court strictement inférieur
à $-1/72$. La conclusion est orientée dans le bon sens : la suppression de
l'attachement augmente strictement la moyenne.

La déclaration `FreezingGrowth.removeAttachClaim : RemoveAttachClaim` n'a
aucune hypothèse supplémentaire. Elle extrait un même $n$ pour les deux
admissibilités et la comparaison d'espérances, avec exactement les mots,
quantificateurs et sens d'inégalité de l'énoncé du papier.

La route est substantiellement différente de la dernière étape du manuscrit :
elle remplace la convergence de tous les accroissements par des petits
accroissements arbitrairement loin, obtenus de la croissance sous-linéaire.
Elle prouve M1iii, et même la propriété de témoins arbitrairement grands,
mais **pas** la comparaison pour tous les grands indices de III10, ni
l'identité/convergence de III9. Ces deux obligations restent distinctes.
Les raccords par profils ne constituent toujours pas une preuve du couplage
des arbres complets avec toutes leurs étiquettes en III1/I2.
