constant symbol Typ: TYPE;
constant symbol int: Typ;

constant symbol id [_:Typ]: Typ → Typ;
notation id prefix 2;

symbol should_not_fail ≔ @id int int;
