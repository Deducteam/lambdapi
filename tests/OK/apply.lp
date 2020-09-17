constant symbol A : TYPE
constant symbol B : TYPE

theorem test1 : (A → B) → A → B
proof
  assume h1 h2
  apply h1
  apply h2
qed

constant symbol C : TYPE

theorem test2 : (A → B → C) → A → B → C
proof
  assume h1 h2 h3
  apply h1
  apply h2
  apply h3
qed

theorem test3 : (A → B → C) → A → B → C
proof
  assume h1 h2 h3
  apply h1
  // print
  focus 1
  // print
  apply h3
  apply h2
qed
