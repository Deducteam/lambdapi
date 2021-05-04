constant symbol Typ: TYPE;
constant symbol int: Typ;

constant symbol id : Typ → Typ → Typ;
notation id infix 2;

symbol should_fail ≔ int @id int;
