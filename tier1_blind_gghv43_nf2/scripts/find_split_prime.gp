read("R_cand.gp");
Rz = R*denominator(content(R));
c = 0;
forprime(p = 30000, 3000000, if (p % 7 != 1 && Mod(denominator(content(R)),p) != 0 && #polrootsmod(Rz, p) == 5, print(p); c++; if (c >= 3, break)));
