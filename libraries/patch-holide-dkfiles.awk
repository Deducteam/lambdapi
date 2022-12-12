BEGIN{print "#REQUIRE STTfa."}
/^type /{next}
/^bool /{next}
/^ind /{next}
/^arr /{next}
/^def term /{next}
/ --> /{next}
/^def proof /{next}
/^imp /{next}
/^forall /{next}
{print}
