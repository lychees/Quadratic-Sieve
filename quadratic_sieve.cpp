#include <gmp.h>
#include <gmpxx.h>
#include <time.h>
#include <bitset>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <cstring>
#include <stack>
#include <vector>
#include <algorithm>
#include <iostream>
#include <thread>
#include <mutex>
#include <sstream>
#define Prime_Sieve_Size 10000000
#define Prime_Pi 664579
#define MORE 5
#define Threads 4
#define possible(x) (fabs(sieve[x]) < threshold)
#define Chunk 8388608

const float Pollard_Rho_Bound = 1e16;

using namespace std;

mpz_class N;

unsigned int Prime[Prime_Pi];

int Base_Count, Vector_Count, Vectors;

int qs_cnt = 0;
bool qs_end = false;
mpz_class qs_factor;

mutex qs_m, si_m;

vector<thread> threads;

long long pow_mod(long long a, long long b, long long n) {
		long long c = 1;
		for ( ; b; b >>= 1, a = a * a % n)
				if (b & 1)
						c = c * a % n;
		return c;
}

int legendre_symbol(long long a, long long p) {
		if (!a) return 0;
		long long t = pow_mod(a, p >> 1, p);
		return t;
}

void tonelli_shanks(long long n, long long p, int &a, int &b) {
		if (p == 2) {
				a = b = n & 1;
				return ;
		}
		long long q = p - 1, s = 0;
		while (!(q & 1)) {
				q >>= 1;
				s ++;
		}
		if (s == 1) {
				a = pow_mod(n, (p + 1) >> 2, p);
				b = p - a;
				return ;
		}
		long long z = 2;
		while (legendre_symbol(z, p) == 1)
				z ++;
		long long c = pow_mod(z, q, p);
		long long r = pow_mod(n, (q + 1) >> 1, p), t = pow_mod(n, q, p);
		while (t != 1) {
				long long i = 1;
				long long u = pow_mod(t, 2, p);
				while (u != 1) {
						i++;
						u = pow_mod(u, 2, p);
				}
				long long b = pow_mod(c, pow_mod(2, s - i - 1, p - 1), p);
				r = r * b % p;
				c = b * b % p;
				t = t * c % p;
				s = i;
		}
		a = r;
		b = p - r;
}

void small_sieve() {
		bool *isprime = new bool[Prime_Sieve_Size];
		memset(isprime, 1, sizeof(bool) * Prime_Sieve_Size);
		int cnt = 0;
		for (unsigned int i = 2; i < Prime_Sieve_Size; i++)
				if (isprime[i]) {
						Prime[cnt++] = i;
						for (unsigned int j = i + i; j < Prime_Sieve_Size; j += i)
								isprime[j] = 0;
				}
		delete [] isprime;
}

inline long long f(long long x, long long &a, long long &n) {
		long long z = 1;
		for (long long i = x; i; i >>= 1, x = (x << 1) % n)
				if (i & 1) z = (z + x) % n;
		return (z + a) % n;
}

long long gcd(long long x, long long y) {
		if (y == 0)	return x;
		return gcd(y, x % y);
}

inline long long mpz_get_ll(mpz_class &x) {
		istringstream in(x.get_str());
		long long n;
		in >> n;
		return n;
}

inline mpz_class mpz_init_set_ll(long long n) {
		ostringstream out;
		out << n;
		mpz_class x;
		mpz_init_set_str(x.get_mpz_t(), out.str().c_str(), 10);
		return x;
}

mpz_class pollard_rho(long long n) {
		long long x = 2, y = 2, d = 1;
		long long a = 1;
		while (d == 1) {
				x = f(x, a, n);
				y = f(f(y, a, n), a, n);
				d = gcd(abs(x - y), n);
				if (d == n) {
						x = 2;
						y = 2;
						d = 1;
						a += 2;
				}
		}
		return mpz_init_set_ll(d);
}

class Gauss {
		private:
				int M, N, m, n, k, r;
				long long **A;
				inline bool getbit(int i, int j) {
						return (A[i][j >> 6] >> (j & 63)) & 1;
				}
				inline int getpos(int j) {
						return j >> 6;
				}
		public:
				int nk;
				mpz_class *P;
				Gauss(int _M, int _N):M(_M) {
						m = M; n = k = nk = 0; N = (_N >> 6) + 2;
						cerr << "Matrix Size " << M << " " << N << "\n";
						A = new long long*[M];
						for (int i = 0; i < M; i++) {
								A[i] = new long long[N];
								memset(A[i], 0, sizeof (long long) * N);
						}
						P = new mpz_class[N << 6];
				}
				~Gauss() {
						for (int i = 0; i < M; i++)
								delete [] A[i];
						delete [] A;
						delete [] P;
				}
				inline bool push(long long *tmp, mpz_class *ptmp) {
						if (n >= N)
								return false;
						for (int i = 0; i < M; i++)
								A[i][n] = tmp[i];
						for (int i = 0; i < 64; i++)
								P[nk++] = ptmp[i];
						n++;
						return true;
				}
				inline bool solution(bool *X, bool *B) {
						int j = nk - 1;
						if (j <= r) return false;
						for (int i = r - 1; i >= 0; i--) {
								while (j > 0 && !getbit(i, j)) {
										X[j] = rand() & 1;
										if (X[j]) {
												for (int k = 0; k < i; k++)
														if (getbit(k, j))
																B[k] ^= 1;
										}
										j--;
								}
								if (getbit(i, j)) {
										if (X[j] = B[i]) {
												for (int k = 0; k < i; k++)
														if (getbit(k, j))
																B[k] ^= 1;
										}
										j--;
								}
						}
						return true;
				}
				void showsolution(bool *X) {
						int len = nk;
						for (int i = 0; i < len; i++)
								cerr << X[i] << " ";
						cerr << "\n";
				}
				bool eliminate() {
						int j = 0, i = 0, p;
						for ( ; i < M; i++) {
								p = -1;
								while (p == -1 && j < nk - 1) {
										for (int k = i; k < M; k++)
												if (getbit(k, j))
														p = k;
										if (p == -1) j++;
								}
								if (p == -1) {
										r = min(j, i);
										return i < j;
								}
								if (p != i) {
										for (int k = getpos(j); k < N; k++) {
												swap(A[p][k], A[i][k]);
										}
								}
								for (int k = i + 1; k < M; k++)
										if (getbit(k, j)) {
												for (int l = getpos(j); l < N; l++)
														A[k][l] ^= A[i][l];
										}
						}
						r = min(j, i);
						return i < j;
				}
				void debug() {
						return ;
						getchar();
						cerr << "M: " << M << "\n";
						cerr << "n: " << n << "\n";
						for (int i = 0; i < M; i++) {
								for (int j = 0; j < nk; j++)
										cerr << (getbit(i, j) ? '1' : ' ') << " ";
						}
						cerr << "\n" << "\n";
				}
				int rank() {
						return r;
				}
};

class Sieve {
		private:
				mpz_class n, sqrtn;
				int Size;
				int Bound;
				float lnn;
				float threshold;
				int *xa, *xb;
				float *log2;
		public:
				vector<int> prime_bases;
				Sieve(mpz_class _n, int size):n(_n), Size(size) {
						prime_bases.push_back(-1);
						sqrtn = sqrt(n);
						lnn = mpz_sizeinbase(n.get_mpz_t(), 2) * log(2);
						Bound = ceil(exp(0.558 * sqrt(lnn * log(lnn)))) + 300;
						cerr << "Bound " << Bound << "\nGenerating prime bases" << "\n";
						for (int i = 0; i < Prime_Pi && Prime[i] < Bound; i++)
								if (mpz_legendre(n.get_mpz_t(), mpz_class(Prime[i]).get_mpz_t()) == 1)
										prime_bases.push_back(Prime[i]);
						Base_Count = prime_bases.size();
						cerr << "Generated " << Base_Count << " prime bases." << "\n";
						cerr << "The max prime base is " << prime_bases[Base_Count - 1] << "\n";
						xa = new int[Base_Count];
						xb = new int[Base_Count];
						log2 = new float[Base_Count];
						xa[0] = xb[0] = 0;	
						xa[1] = xb[1] = 1;	
						cerr << "Tonelli-Shanks algorithm" << "\n";
						mpz_class u;
						for (int i = 2; i < Base_Count; i++) {
								int p = prime_bases[i];
								u = n % p;
								tonelli_shanks(u.get_si(), p, xa[i], xb[i]);
								log2[i] = log(p) / log(2);
						}
						threshold = log2[Base_Count - 1];
				}
				~Sieve() {
						delete [] xa;
						delete [] xb;
						delete [] log2;
				}
				bool dosieve(const mpz_class& minx, int size, float *sieve) {
						if (size > Size) {
								cerr << "Not enough size" << "\n";
								return false;
						}
						mpz_class p;
						for (int i = 0; i < size; i++) {
								p = minx + i;
								p = p * p - n;
								sieve[i] = mpz_sizeinbase(p.get_mpz_t(), 2);
						}
						mpz_class start;
						for (int i = 1; i < Base_Count; i++) {
								int p = prime_bases[i];
								start = minx % p;
								int t = start.get_si(), a = xa[i];
								if ((a -= t) < 0) a += p;
								float log2p = log2[i];
								for (int j = a; j < size; j += p)
										sieve[j] -= log2p;
								if (i == 1) continue ;
								if ((a = xb[i] - t) < 0) a += p;
								for (int j = a; j < size; j += p)
										sieve[j] -= log2p;
						}
				}
				inline bool factor(mpz_class x, int *V) {
						if (x < 0) {
								V[0]++;
								x = -x;
						}
						for (int i = 1; i < Base_Count && x >= prime_bases[i]; i++)
								if (x % prime_bases[i] == 0) {
										x /= prime_bases[i];
										V[i]++;
										while (x % prime_bases[i] == 0) {
												x /= prime_bases[i];
												V[i]++;
										}
								}
						return x == 1;
				}
				inline int select(const mpz_class& minx, int start, int end, int *V, long long *tmp, mpz_class *ptmp, float *sieve, int &cap) {
						mpz_class x, y;
						for (int i = start; i < end ; i++)
								if (possible(i)) {
										x = minx + i;
										y = x * x - n;
										memset(V, 0, sizeof (int) * Base_Count);
										if (factor(y, V)) {
												ptmp[cap] = x;
												for (int j = 0; j < Base_Count; j++)
														if (V[j] & 1)
																tmp[j] |= 1LL << cap;
												if (++cap == 64)
														return i + 1;
										}
								}
						return Size;
				}
};

void gambler(Gauss *G, Sieve *S, const mpz_class& n) {
		int *V = new int[Base_Count];
		bool *X = new bool[Vector_Count];
		bool *B = new bool[Vector_Count];
		time_t start, end;
		while (!qs_end) {
				start = clock();
				memset(B, 0, sizeof (bool) * Vector_Count);
				if (G->solution(X, B) && !qs_end) {
						mpz_class x = 1, y = 1, t, p;
						memset(V, 0, sizeof (int) * Base_Count);
						for (int i = 0; i < Vector_Count; i++)
								if (X[i]) {
										p = G->P[i];
										x = x * p % n;
										S->factor(p * p - n, V);
								}
						for (int i = 1 ; i < Base_Count; i++)
								if (V[i]) {
										p = S->prime_bases[i];
										if (V[i] > 2) {
												mpz_powm_ui(p.get_mpz_t(), p.get_mpz_t(), V[i] >> 1, n.get_mpz_t());
												y = y * p % n;
										} else y = y * p % n;
								}
						t = x - y;
						if (t < 0) t = -t;
						mpz_gcd(p.get_mpz_t(), t.get_mpz_t(), n.get_mpz_t());
						end = clock();
						if (qs_end)
								break;
						qs_m.lock();
						qs_cnt ++;
						if (qs_cnt & 15 == 0)
								cerr << (end - start) / 1000000.0 << "s to guess " << qs_cnt << " factor\t" << x << " " << y << "\n";
						if (p != 1 && p != n) {
								cerr << "Found a factor after " << qs_cnt << " guesses" << "\n";
								qs_end = true;
								qs_factor = p;
								break ;
						}
						qs_m.unlock();
				}
		}
		delete [] X;
		delete [] B;
		delete [] V;
}

void king(Gauss *G, Sieve *S, mpz_class minx) {
		int *V = new int[Base_Count];
		long long *tmp = new long long[Base_Count];
		memset(tmp, 0, sizeof (long long) * Base_Count);
		float *sieve = new float[Chunk];
		mpz_class *ptmp = new mpz_class[64];
		memset(ptmp, 0, sizeof (mpz_class) * 64);
		int cap = 0;
		float percent = 1e2 / Vectors;
		while (G->nk < Vectors) {
				S->dosieve(minx, Chunk, sieve);
				int now = 0;
				while ((now = S->select(minx, now, Chunk, V, tmp, ptmp, sieve, cap)) != Chunk) {
						if (cap == 64) {
								si_m.lock();
								bool res = G->push(tmp, ptmp);
								//cerr << " Total " << G->nk << "\t\t" << percent * G->nk << "%\n";
								printf("%.2f%%\n", percent * G->nk);
								si_m.unlock();
								cap = 0;
								memset(tmp, 0, sizeof (long long) * Base_Count);
								if (!res) break;
						}
				}
				minx += Threads * Chunk;
		}
		delete [] ptmp;
		delete [] sieve;
		delete [] tmp;
		delete [] V;
}

mpz_class quadratic_sieve(mpz_class& n) {
		int Size = Chunk;

		Sieve *S = new Sieve(n, Size);
		Gauss *G = new Gauss(Base_Count, Base_Count + MORE);

		Vectors = (((Base_Count + MORE) >> 6) + 2) << 6;
		Vector_Count = 0;

		mpz_class sqrtn = sqrt(n);
		clock_t start = clock();
		float percent = 1e2 / Vectors;

		for (int i = 0; i < Threads; i++)
				threads.push_back(thread(king, G, S, sqrtn + i * Chunk));
		for (auto& thread : threads)
				thread.join();
		threads.clear();

		Vector_Count = Vectors;

		clock_t end = clock();
		cerr << (end - start) / 1000000.0 << "s to build matrix" << "\n";
		G->debug();
		cerr << "I'm eliminating the matrix..." << "\n";
		start = clock();
		if (G->eliminate()) {
				end = clock();
				cerr << (end - start) / 1000000.0 << "s to eliminate" << "\n";
				cerr << "The rank of the matrix is " << G->rank() << "\n";
				G->debug();
				cerr << "Now let's guess a factor" << "\n";
				qs_cnt = 0;
				qs_end = false;
				for (int i = 0; i < Threads; i++)
						threads.push_back(thread(gambler, G, S, n));
				for (auto & thread : threads) {
						thread.join();
				}
				return qs_factor;
		} else {
				cerr << "Elimination Failed" << "\n";
		}
		return 1;
}
int main()
{
		srand(time(NULL));
		long long a, b;
		small_sieve();
		long long lln;
		cin >> N;
		cerr << "Factoring " << N << "\n";
		for (int i = 0; i < Prime_Pi; i++)
				if (mpz_divisible_ui_p(N.get_mpz_t(), Prime[i])) {
						cerr << Prime[i] << "\n";
						mpz_divexact_ui(N.get_mpz_t(), N.get_mpz_t(), Prime[i]);
				}
		stack<mpz_class> factors;
		if (N != 1)
				factors.push(N);
		while (!factors.empty()) {
				mpz_class factor = factors.top();
				factors.pop();
				if (mpz_probab_prime_p(factor.get_mpz_t(), 10)) {
						cerr << factor << "\n";
						continue ;
				}
				if (factor < Pollard_Rho_Bound) {
						mpz_class f = pollard_rho(mpz_get_ll(factor));
						factors.push(f);
						factors.push(factor / f);
						continue ;
				}
				if (mpz_perfect_power_p(factor.get_mpz_t())) {
						mpz_class root, rem;
						unsigned int l = mpz_sizeinbase(factor.get_mpz_t(), 2) / 2;
						for (unsigned int i = l; i > 2; i--) {
								mpz_rootrem(root.get_mpz_t(), rem.get_mpz_t(), factor.get_mpz_t(), i);
								if (rem == 0) {
										factors.push(root);
										break ;
								}
						}
						continue ;
				}
				mpz_class f = quadratic_sieve(factor);
				factors.push(f);
				factors.push(factor / f);
		}
}
