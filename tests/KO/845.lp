// test that a notation is compatible with the type
symbol O : TYPE;
symbol T : O;
symbol p : O → TYPE;
symbol ¬  : p T → p T → p T;
symbol ⊥ : p T;
symbol ⊤ : p T;
notation ⊤ infix left 5;
//rule _ ⊤ _ ↪ ¬ ⊥;
