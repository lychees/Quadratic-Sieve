quadratic_sieve : quadratic_sieve.cpp
	g++ -std=c++11 -o quadratic_sieve quadratic_sieve.cpp -lgmp -lgmpxx -lpthread -O2
