   symbol N:TYPE;

   // with no proof script
   symbol add : N → N → N; // a type but no definition (axiom)
   symbol double n ≔ add n n; // no type but a definition
   symbol triple n : N ≔ add n (double n); // a type and a definition

   // with a proof script (theorem or interactive definition)
   symbol F : N → TYPE;
   symbol idF n : F n → F n ≔
   begin
     assume n x;
     apply x
   end;
