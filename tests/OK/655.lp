constant symbol Typ: TYPE;
constant symbol int: Typ;

constant symbol id : Typ → Typ → Typ;
notation id infix 2;

symbol normal ≔ @id int int;

constant symbol id2 : Typ → Typ → Typ;
notation id2 prefix 3;

symbol should_not_fail ≔ @id2 int int;
