constant symbol A : TYPE;
constant symbol B : TYPE;

opaque symbol test1 : (A → B) → A → B
≔ begin
  assume h1 h2;
  apply h1;
  apply h2;
end

constant symbol C : TYPE;

opaque symbol test2 : (A → B → C) → A → B → C
≔ begin
  assume h1 h2 h3;
  apply h1;
  apply h2;
  apply h3;
end
