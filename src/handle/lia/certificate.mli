val find : Checker.constraint_ array -> Checker.certificate option
(** Recherche complète et terminante de certificats de Farkas entiers.

    Pour les inégalités [a_i · x + c_i <= 0], renvoie des entiers
    [lambda_i >= 0] tels que [sum lambda_i*a_i = 0] et [sum lambda_i*c_i > 0].
    [None] signifie qu'aucun certificat de cette forme n'existe; cela ne
    signifie pas que le système est satisfiable sur Z. *)
