- Stocker les instances en mémoire (style Elpi accumulate ou bien en ml directement? (Est-ce qu'il y a une différence?))
  + Dans elpi_handle.ml, déclarer compile comme fonction appelable (où l'écrire dedans directement dans le LPcode? est-ce que c'est du LPcode libre? Après ça a du sens que ce soit dans tcsolver.elpi malgré tout.), et remplacer la liste d'instances par une liste de règles en modifiant dans handle/command le code pour instance par un appel à Elpi_handle.compile.
- Classes avec plusieurs arguments (A voir à quel point c'est nécessaire, Isabelle c'est seulement un argument)
- Modulo rewriting (lp unify args with instance rules ?)
  + Quel est le soucis ? on souhaite utiliser en même temps l'unification de Elpi et la réécriture ?
- Rocq-style: add bound variables to search space
- Pour Frédéric: Où est le lambdapi.pkg ??? voir essais dans handle/elpi_handle.ml, fonction init().
  Plus généralement, (pour plus tard) implémenter le fait de pouvoir load des fichiers elpi via leur path relatif au pkg (il suffit de savoir comment ça fonctionne pour les modules)
- Pour Enrico: A quel point il serait difficile de rajouter ce qu'il faut pour pouvoir écrire des tactiques ou autres meta-programmes en Elpi?
  + Surtout tactiques: La différence entre le langage de tactiques (qui a le mérite d'exister) de lambdapi et Ltac ou Ltac2 fait que même pour des tactiques simples on aimerait peut-être avoir quelque chose comme Elpi pour gérer du pattern-matching (+ lambdapi n'a pas trop de tactiques automatiques, Elpi serait évidemment bien utile pour coder de la recherche de preuve style auto de Rocq, même sommaire. ). 