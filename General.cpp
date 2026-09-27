#include <bits/stdc++.h>
using namespace std;

// Type aliases
using ll = long long;
using ull = unsigned long long;
using ld = long double;
using pr = pair<long,long>;
using max_heap = priority_queue<long long>;
using min_heap = priority_queue<long long, vector<long long>, greater<long long>>;
// Fast I/O
#define FAST_IO ios::sync_with_stdio(false); cin.tie(nullptr);cout.tie(nullptr);
// Shortcuts
#define pb push_back
#define eb emplace_back
#define ff first
#define ss second
#define all(x) (x).begin(), (x).end()
#define rall(x) (x).rbegin(), (x).rend()
#define nl "\n"

#define rep(i,a,b) for(int i=(a); i<(b); i++)
#define per(i,a,b) for(int i=(a); i>=(b); i--)
#define vec(n,a) vector<ll>a(n);
#define inp(a) for(auto&x:a)cin>>x;

// Debug (only active when compiled with -DLOCAL)
#ifdef LOCAL
#define dbg(x) cerr << #x << " = " << (x) << nl
#else
#define dbg(x)
#endif

const int dx4[] = {1,-1,0,0};
const int dy4[] = {0,0,1,-1};
const int dx8[] = {1,-1,0,0,1,1,-1,-1};
const int dy8[] = {0,0,1,-1,1,-1,1,-1};

// GCD & LCM
ll gcdll(ll a, ll b){
    return b ? gcdll(b, a % b) : a;
}

ll lcmll(ll a, ll b){
    return a / gcdll(a, b) * b;
}
ll extgcd(ll a, ll b, ll &x, ll &y){
    if(b == 0){ x = 1; y = 0; return a; }
    ll x1, y1;
    ll g = extgcd(b, a % b, x1, y1);
    x = y1;
    y = x1 - (a / b) * y1;
    return g;
}

const ll MOD = 1e9+7;
const ll MAX = 1e5 + 100;
ll fact[MAX];
ll invFact[MAX];
long long power(long long base, long long exp, ll mod = MOD) {
    long long res = 1;
    base %= mod;
    if (base < 0) base += mod;
    while (exp > 0) {
        if (exp % 2 == 1) res = (res * base) % mod;
        base = (base * base) % mod;
        exp /= 2;
    }
    return res;
}
long long modInv(long long n) {
    return power(n, MOD - 2);
}

void pre() {
    fact[0] = 1;
    invFact[0] = 1;
    for (int i = 1; i < MAX; i++){
        fact[i] = (fact[i - 1] * i) % MOD;
    }
    invFact[MAX - 1] = modInv(fact[MAX - 1]);
    for(int i = MAX - 2; i >= 1; i--){
        invFact[i] = (invFact[i + 1] * (i + 1)) % MOD;
    }
}

long long nPr(int n, int r) {
    if (r < 0 || r > n) return 0;
    return (fact[n] * invFact[n - r]) % MOD;
}
long long nCr(int n, int r) {
    if (r < 0 || r > n) return 0;
    return (fact[n] * invFact[r] % MOD * invFact[n - r]) % MOD;
}

pair<ll,ll> findFirstAndSecondMax(const vector<ll>& arr) {
    ll first_max = LLONG_MIN;
    ll second_max = LLONG_MIN;

    for (auto num : arr) {
        if (num > first_max) {
            second_max = first_max;
            first_max = num;
        }
        else if (num > second_max && num != first_max) {
            second_max = num;
        }
    }
    return {first_max, second_max};
}
#define MAXN 200000
int spf[MAXN+1];
void preSpf(){
    for(int i=0;i<=MAXN;i++){
        spf[i]=i;
    }
    for(int i=2;i*i<=MAXN;i++){
        if(spf[i]==i){
            for(int j=i*i; j<=MAXN; j+=i){
                if(spf[j]==j){
                    spf[j]=i;
                }
            }
        }
    }
}
map<int,int> factorize(int n){
    map<int,int> f;
    while(n > 1){
        f[spf[n]]++;
        n /= spf[n];
    }
    return f;
}
vector<int> primesUpTo(int n){
    vector<int> res;
    for(int i=2;i<=n;i++) if(spf[i]==i) res.pb(i);
    return res;
}

struct DSU {
    vector<int> par, rnk, sz;
    DSU(int n){
        par.resize(n); rnk.assign(n,0); sz.assign(n,1);
        iota(all(par), 0);
    }
    int find(int x){
        while(par[x] != x){
            par[x] = par[par[x]];
            x = par[x];
        }
        return x;
    }
    bool unite(int a, int b){
        a = find(a); b = find(b);
        if(a == b) return false;
        if(rnk[a] < rnk[b]) swap(a,b);
        par[b] = a;
        sz[a] += sz[b];
        if(rnk[a] == rnk[b]) rnk[a]++;
        return true;
    }
    bool connected(int a, int b){ return find(a) == find(b); }
    int size(int x){ return sz[find(x)]; }
};
struct Fenwick {
    int n;
    vector<ll> bit;
    Fenwick(int n): n(n), bit(n+1, 0) {}
    void update(int i, ll val){
        for(; i <= n; i += i & (-i)) bit[i] += val;
    }
    ll query(int i){ // prefix sum [1..i]
        ll s = 0;
        for(; i > 0; i -= i & (-i)) s += bit[i];
        return s;
    }
    ll rangeQuery(int l, int r){
        if(l > r) return 0;
        return query(r) - query(l-1);
    }
};
struct SegTree {
    int n;
    vector<ll> tree;
    SegTree(int n): n(n), tree(4*n, 0) {}
    SegTree(const vector<ll>& a): n(a.size()), tree(4*a.size(), 0) {
        build(a, 1, 0, n-1);
    }
    void build(const vector<ll>& a, int node, int l, int r){
        if(l == r){ tree[node] = a[l]; return; }
        int mid = (l+r)/2;
        build(a, 2*node, l, mid);
        build(a, 2*node+1, mid+1, r);
        tree[node] = tree[2*node] + tree[2*node+1];
    }
    void update(int node, int l, int r, int pos, ll val){
        if(l == r){ tree[node] = val; return; }
        int mid = (l+r)/2;
        if(pos <= mid) update(2*node, l, mid, pos, val);
        else update(2*node+1, mid+1, r, pos, val);
        tree[node] = tree[2*node] + tree[2*node+1];
    }
    void update(int pos, ll val){ update(1, 0, n-1, pos, val); }
    ll query(int node, int l, int r, int ql, int qr){
        if(qr < l || r < ql) return 0;
        if(ql <= l && r <= qr) return tree[node];
        int mid = (l+r)/2;
        return query(2*node, l, mid, ql, qr) + query(2*node+1, mid+1, r, ql, qr);
    }
    ll query(int ql, int qr){ return query(1, 0, n-1, ql, qr); }
};
vector<vector<int>> adj; 
void bfs(int src, vector<int>& dist){
    dist.assign(adj.size(), -1);
    queue<int> q;
    dist[src] = 0;
    q.push(src);
    while(!q.empty()){
        int u = q.front(); q.pop();
        for(int v : adj[u]){
            if(dist[v] == -1){
                dist[v] = dist[u] + 1;
                q.push(v);
            }
        }
    }
}
void dfs(int u, vector<int>& vis){
    vis[u] = 1;
    for(int v : adj[u]){
        if(!vis[v]) dfs(v, vis);
    }
}

struct custom_hash {
    static uint64_t splitmix64(uint64_t x){
        x += 0x9e3779b97f4a7c15ULL;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
        x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
        return x ^ (x >> 31);
    }
    size_t operator()(uint64_t x) const {
        static const uint64_t FIXED_RANDOM =
            chrono::steady_clock::now().time_since_epoch().count();
        return splitmix64(x + FIXED_RANDOM);
    }
};

int main(){
    FAST_IO;
    int T;
    cin >> T;
    while(T--){
        int n;
        cin>>n;
        vec(n,a)
        inp(a)


    }

    return 0;
}