log2(n)={log(n)/log(2)}

randp(k)={n=2^k;n+=random(n);while(!isprime(n),n++);n}

randnum(k)={a=randp(k);b=randp(k);print(a);print(b);a*b}
