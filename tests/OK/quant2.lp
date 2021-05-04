// test parsing of quantifiers
symbol A:TYPE;
symbol f:(A → A) → A;
compute `f x, x;
symbol ⇒:A → A → A; notation ⇒ infix right 10;
compute `f x, `f y, x ⇒ y;
symbol a:A;
compute a ⇒ `f x, x;
compute a ⇒ `f x, a ⇒ `f y, x ⇒ y;
