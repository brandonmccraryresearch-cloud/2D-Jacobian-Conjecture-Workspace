read("R_cand.gp");
Rz = R*denominator(content(R));
v = polredabs(Rz, 1);
Rr = subst(v[1], u, w);
a = subst(lift(v[2]), u, w);
print("RR ", Vec(Rr));
print("PSI ", Vec(a));
print("CHECK Rz(psi(w)) == 0 mod Rr(w): ", subst(Rz, u, Mod(a, Rr)) == 0);
