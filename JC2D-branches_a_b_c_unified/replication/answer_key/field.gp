\\ field.gp -- invariants of the top-layer field (answer key R3). Run: gp -q field.gp < /dev/null
R = x^5 - x^4 + 3*x^3 + 3*x^2 + 26;
V = 9374377445732*x^5 + 62410476400737833472*x^4 + 265472843532245531128968765*x^3 + 591414847960503971284831143987840*x^2 + 586529490054134032292876680565455306752*x - 1888043347611739526396142670327809715470336;
print("R irreducible over Q: ", polisirreducible(R));
print("polredabs(R) == R: ", polredabs(R) == R);
print("V irreducible: ", polisirreducible(V), "   polredabs(V) == R: ", polredabs(V) == R);
print("V(t^7) irreducible (degree 35): ", polisirreducible(subst(V, x, x^7)));
print("real roots: R ", polsturm(R), ", V ", polsturm(V), ", V(t^7) ", polsturm(subst(V, x, x^7)));
K = nfinit(R);
print("field discriminant: ", K.disc, " = ", factor(K.disc));
print("signature (r1, r2): ", K.sign);
print("Galois group of R: ", polgalois(R));
print("class number: ", bnfinit(R, 1).no);
