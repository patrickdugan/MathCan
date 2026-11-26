/* DETFACT-09: native bounded-payload exponent execution, synthetic audit. */
#define _POSIX_C_SOURCE 200809L
#include <gmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <limits.h>
#include <time.h>
#include <sys/resource.h>

static size_t live, peak, g_live, g_peak, own_live, own_peak, budget;
static unsigned long long allocs, pow_calls, prime_powers, mark_writes, segs;
static size_t max_exp_bits;
static void die(const char *msg, int code) { fprintf(stderr,"%s\n",msg); exit(code); }
static void charge(size_t old, size_t n, int gmp) {
    if (old>live || n>SIZE_MAX-(live-old)) die("accounting overflow",4);
    if (budget && live-old+n>budget) die("workspace budget exhausted",3);
    live=live-old+n; if(live>peak) peak=live;
    size_t *v=gmp?&g_live:&own_live, *h=gmp?&g_peak:&own_peak;
    if(old>*v) die("accounting underflow",4);
    *v=*v-old+n; if(*v>*h)*h=*v; ++allocs;
}
static void *gm_alloc(size_t n){charge(0,n,1);void *p=malloc(n?n:1);if(!p)die("allocation failure",4);return p;}
static void *gm_realloc(void *p,size_t old,size_t n){charge(old,n,1);void *r=realloc(p,n?n:1);if(!r)die("allocation failure",4);return r;}
static void gm_free(void *p,size_t n){if(n>g_live||n>live)die("free accounting",4);g_live-=n;live-=n;free(p);}
static void *own_alloc(size_t n){charge(0,n,0);void*p=malloc(n?n:1);if(!p)die("allocation failure",4);return p;}
static void own_free(void*p,size_t n){if(n>own_live||n>live)die("free accounting",4);own_live-=n;live-=n;free(p);}
static unsigned long num(const char *s){char *e;errno=0;if(!s[0]||s[0]=='-')die("invalid integer",2);unsigned long x=strtoul(s,&e,10);if(errno||*e)die("invalid integer",2);return x;}
static unsigned long root_floor(unsigned long x){unsigned long a=0,b=x<4294967295UL?x:4294967295UL;while(a<b){unsigned long m=a+(b-a+1)/2;if(m<=x/m)a=m;else b=m-1;}return a;}
static unsigned long bits_ul(unsigned long n){unsigned long b=0;while(n){++b;n>>=1;}return b;}
static void power(mpz_t r,const mpz_t e,const mpz_t N){size_t w=mpz_sizeinbase(e,2);if(w>max_exp_bits)max_exp_bits=w;mpz_powm(r,r,e,N);++pow_calls;}
static double clock_s(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}

int main(int argc,char **argv){
    /* mode K segment_bytes chunk_bits batch budget_bytes N Mstar */
    if(argc!=9)die("usage: native_audit explicit|stream K S W batch budget N Mstar",2);
    int explicit_mode=!strcmp(argv[1],"explicit");if(!explicit_mode&&strcmp(argv[1],"stream"))die("mode",2);
    unsigned long K=num(argv[2]),S=num(argv[3]),W=num(argv[4]),B=num(argv[5]);budget=num(argv[6]);
    if(K<1||K>100000000UL||S<1||S>100000000UL||W<1||W>10000000UL||B<1||B>1024)die("domain",2);
    mp_set_memory_functions(gm_alloc,gm_realloc,gm_free);
    double start=clock_s();
    mpz_t N,M,u,chunk,e,tmp,g;mpz_inits(N,M,u,chunk,e,tmp,g,NULL);
    if(mpz_set_str(N,argv[7],10)||mpz_set_str(M,argv[8],10)||mpz_cmp_ui(N,3)<0||mpz_sgn(M)<=0)die("domain",2);
    mp_bitcnt_t v=mpz_scan1(M,0);unsigned long s=1+v+bits_ul(K)-1;mpz_fdiv_q_2exp(u,M,v);mpz_set_ui(chunk,1);
    mpz_t *xs=own_alloc(B*sizeof(*xs));for(unsigned long i=0;i<B;i++){mpz_init_set_ui(xs[i],i+2);mpz_mod(xs[i],xs[i],N);if(!explicit_mode)power(xs[i],u,N);}
    unsigned long r=root_floor(K),np=0;unsigned char *small=own_alloc(r+1);memset(small,1,r+1);small[0]=0;if(r>=1)small[1]=0;
    for(unsigned long p=2;p<=r/p;p++)if(small[p])for(unsigned long j=p*p;j<=r;j+=p)small[j]=0;
    for(unsigned long p=3;p<=r;p+=2)np+=small[p]!=0;
    unsigned long *ps=own_alloc(np*sizeof(*ps));for(unsigned long p=3,i=0;p<=r;p+=2)if(small[p])ps[i++]=p;
    own_free(small,r+1);
    unsigned long span=K>=3?(K-3)/2+1:0;if(span>S)span=S;
    unsigned char *mark=own_alloc(span);
    /* Explicit balanced carry product. Fixed 32 slots cover K<=1e8. */
    mpz_t slots[32];unsigned char used[32]={0};if(explicit_mode)for(int i=0;i<32;i++)mpz_init(slots[i]);
    for(unsigned long lo=3;lo<=K;lo+=2*S){
        unsigned long count=(K-lo)/2+1;if(count>S)count=S;unsigned long hi=lo+2*(count-1);memset(mark,1,count);++segs;
        for(unsigned long i=0;i<np;i++){unsigned long p=ps[i];if(p>hi/p)break;unsigned long first=((lo+p-1)/p)*p;if(first<p*p)first=p*p;if(!(first&1))first+=p;for(unsigned long j=(first-lo)/2;j<count;j+=p){mark[j]=0;++mark_writes;}}
        for(unsigned long i=0;i<count;i++)if(mark[i]){
            unsigned long p=lo+2*i,q=p;while(q<=K/p)q*=p;++prime_powers;
            if(explicit_mode){mpz_set_ui(e,q);int j=0;while(j<32&&used[j]){mpz_mul(e,e,slots[j]);mpz_clear(slots[j]);mpz_init(slots[j]);used[j++]=0;}if(j==32)die("slot overflow",4);mpz_swap(e,slots[j]);used[j]=1;}
            else {
                if(mpz_cmp_ui(chunk,1)>0 && mpz_sizeinbase(chunk,2)+bits_ul(q)>W){for(unsigned long j=0;j<B;j++)power(xs[j],chunk,N);mpz_set_ui(chunk,1);}
                if(bits_ul(q)>W){mpz_set_ui(e,q);for(unsigned long j=0;j<B;j++)power(xs[j],e,N);}
                else {mpz_mul_ui(chunk,chunk,q);if(mpz_sizeinbase(chunk,2)>W)die("chunk invariant",4);}
            }
        }
        /* Segment boundary allows checkpoint at flushed prefix. */
        if(!explicit_mode&&mpz_cmp_ui(chunk,1)>0){for(unsigned long j=0;j<B;j++)power(xs[j],chunk,N);mpz_set_ui(chunk,1);}
    }
    own_free(mark,span);own_free(ps,np*sizeof(*ps));
    if(explicit_mode){for(int j=0;j<32;j++){if(used[j])mpz_mul(u,u,slots[j]);mpz_clear(slots[j]);}mpz_clear(e);mpz_init(e);for(unsigned long j=0;j<B;j++)power(xs[j],u,N);}
    double elapsed=clock_s()-start;
    printf("{\"seconds\":%.9f,\"peak_payload_bytes\":%zu,\"gmp_peak_bytes\":%zu,\"own_peak_bytes\":%zu,\"allocation_events\":%llu,\"max_exponent_bits\":%zu,\"pow_calls\":%llu,\"prime_powers\":%llu,\"mark_writes\":%llu,\"segments\":%llu,\"s\":%lu,\"residues\":[",elapsed,peak,g_peak,own_peak,allocs,max_exp_bits,pow_calls,prime_powers,mark_writes,segs,s);
    for(unsigned long j=0;j<B;j++){if(j)putchar(',');gmp_printf("\"%Zd\"",xs[j]);}
    printf("],\"splits\":[");
    for(unsigned long j=0;j<B;j++){
        if(j)putchar(',');
        mpz_set_ui(tmp,j+2);mpz_gcd(g,tmp,N);long idx=-1;
        if(mpz_cmp_ui(g,1)<=0||mpz_cmp(g,N)>=0){idx=-2;for(unsigned long h=0;h<=s;h++){mpz_sub_ui(tmp,xs[j],1);mpz_gcd(g,tmp,N);if(mpz_cmp_ui(g,1)>0&&mpz_cmp(g,N)<0){idx=(long)h;break;}if(h<s){mpz_mul(xs[j],xs[j],xs[j]);mpz_mod(xs[j],xs[j],N);}}}
        if(idx==-2)printf("null");else gmp_printf("[%ld,\"%Zd\"]",idx,g);
    }
    for(unsigned long j=0;j<B;j++)mpz_clear(xs[j]);
    own_free(xs,B*sizeof(*xs));mpz_clears(N,M,u,chunk,e,tmp,g,NULL);
    struct rusage ru;getrusage(RUSAGE_SELF,&ru);
    printf("],\"peak_payload_full_run_bytes\":%zu,\"peak_rss_kib\":%ld,\"live_after_clear_bytes\":%zu}\n",peak,ru.ru_maxrss,live);
    if(live)die("allocation leak",4);
    return 0;
}
