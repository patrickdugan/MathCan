/* DETFACT-12: fixed-arena synthetic modular execution; no GMP. */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <sys/resource.h>
#include <inttypes.h>
#include <limits.h>

typedef uint32_t limb;
static size_t L;
static limb *N,*one,*base,*normal,*g,*h,*t;
static uint64_t muls,pows;
static void fail(const char *s,int code){fprintf(stderr,"%s\n",s);exit(code);}
static uint64_t num(const char*s){char*e;errno=0;if(!*s||*s=='-')fail("integer",2);uint64_t n=strtoull(s,&e,10);if(errno||*e)fail("integer",2);return n;}
static unsigned nib(char c){if(c>='0'&&c<='9')return c-'0';if(c>='a'&&c<='f')return c-'a'+10;fail("canonical lowercase hex",2);return 0;}
static size_t hexlen(const char*s){size_t n=strlen(s);if(!n||n>1024||nib(s[0])==0)fail("hex domain",2);for(size_t i=1;i<n;i++)(void)nib(s[i]);return n;}
static void parse(limb*a,const char*s,size_t len){for(size_t j=0;j<len;j++)a[j/8]|=(limb)nib(s[len-1-j])<<(4*(j%8));}
static unsigned ubits(uint64_t n){unsigned r=0;while(n){n>>=1;r++;}return r;}
static uint64_t root(uint64_t k){uint64_t r=0;while((r+1)<=k/(r+1))r++;return r;}
static int cmp(const limb*a,const limb*b){for(size_t i=L;i-->0;)if(a[i]!=b[i])return a[i]>b[i]?1:-1;return 0;}
static int zero(const limb*a){for(size_t i=0;i<L;i++)if(a[i])return 0;return 1;}
static int isone(const limb*a){if(a[0]!=1)return 0;for(size_t i=1;i<L;i++)if(a[i])return 0;return 1;}
static limb sub(limb*a,const limb*b){uint64_t borrow=0;for(size_t i=0;i<L;i++){uint64_t x=a[i],y=(uint64_t)b[i]+borrow;a[i]=(limb)(x-y);borrow=x<y;}return (limb)borrow;}
static void shr(limb*a){limb c=0;for(size_t i=L;i-->0;){limb d=a[i]&1;a[i]=(a[i]>>1)|(c<<31);c=d;}}
static void dbl(limb*a){limb c=0;for(size_t i=0;i<L;i++){limb d=a[i]>>31;a[i]=(a[i]<<1)|c;c=d;}if(c||cmp(a,N)>=0){limb b=sub(a,N);if(b!=c)fail("doubling invariant",4);}}
static void tomont(limb*a){for(size_t j=0;j<32*L;j++)dbl(a);}
static limb ninv;
static void mont(limb*out,const limb*a,const limb*b){
    memset(t,0,(2*L+2)*sizeof(*t));
    for(size_t i=0;i<L;i++){
        uint64_t c=0;for(size_t j=0;j<L;j++){uint64_t x=(uint64_t)a[i]*b[j]+t[i+j]+c;t[i+j]=(limb)x;c=x>>32;}
        for(size_t j=i+L;c;j++){if(j>=2*L+2)fail("product width",4);uint64_t x=(uint64_t)t[j]+c;t[j]=(limb)x;c=x>>32;}
    }
    for(size_t i=0;i<L;i++){
        limb q=t[i]*ninv;uint64_t c=0;
        for(size_t j=0;j<L;j++){uint64_t x=(uint64_t)q*N[j]+t[i+j]+c;t[i+j]=(limb)x;c=x>>32;}
        for(size_t j=i+L;c;j++){if(j>=2*L+2)fail("reduction width",4);uint64_t x=(uint64_t)t[j]+c;t[j]=(limb)x;c=x>>32;}
        if(t[i])fail("reduction invariant",4);
    }
    memcpy(out,t+L,L*sizeof(*out));limb hi=t[2*L];if(t[2*L+1]||hi>1)fail("Montgomery bound",4);
    if(hi||cmp(out,N)>=0){limb br=sub(out,N);if(br!=hi)fail("Montgomery subtraction",4);}
    if(cmp(out,N)>=0)fail("Montgomery range",4);
    muls++;
}
static void setsmall(limb*a,uint64_t x){memset(a,0,L*sizeof(*a));if(L==1)x%=N[0];a[0]=(limb)x;if(L>1)a[1]=(limb)(x>>32);if(cmp(a,N)>=0)fail("base range",4);}
static void power(limb*x,uint64_t q){if(q==1)return;memcpy(base,x,L*sizeof(*x));for(unsigned j=ubits(q)-1;j-->0;){mont(x,x,x);if((q>>j)&1)mont(x,x,base);}pows++;}
static unsigned bit(const limb*a,size_t j){return (a[j/32]>>(j%32))&1u;}
static void bigpower(limb*x,const limb*e,size_t top,size_t bottom){memcpy(base,x,L*sizeof(*x));for(size_t j=top;j-->bottom;){mont(x,x,x);if(bit(e,j))mont(x,x,base);}pows++;}
static void unmont(limb*out,const limb*x){setsmall(base,1);mont(out,x,base);}
static void gcdfixed(const limb*a){memcpy(g,a,L*sizeof(*g));memcpy(h,N,L*sizeof(*h));while(!zero(g)){while(!(g[0]&1))shr(g);if(cmp(g,h)<0){/* swap by scalar to keep fixed storage */for(size_t i=0;i<L;i++){limb x=g[i];g[i]=h[i];h[i]=x;}}sub(g,h);} }
static void printhex(const limb*a){size_t i=L;while(i>1&&!a[i-1])i--;printf("%" PRIx32,a[--i]);while(i>0)printf("%08" PRIx32,a[--i]);}
static double now(void){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec+ts.tv_nsec*1e-9;}
int main(int argc,char**argv){
    /* K, segment odd slots, chunk width, batch, arena cap (0 uncapped), N hex, Mstar hex */
    if(argc!=8)fail("usage: arena_audit K S W B cap N_hex Mstar_hex",2);
    uint64_t K=num(argv[1]),S=num(argv[2]),W=num(argv[3]),B=num(argv[4]),cap=num(argv[5]);
    if(K<1||K>10000000||S<1||S>10000000||W<1||W>64||B<1||B>128)fail("domain",2);
    size_t nl=hexlen(argv[6]),el=hexlen(argv[7]);if(!(nib(argv[6][nl-1])&1)||(nl==1&&nib(argv[6][0])<3))fail("odd N >=3",2);
    L=(nl+7)/8;size_t E=(el+7)/8;uint64_t r=root(K),span=(K-1)/2;if(span>S)span=S;
    /* All explicit algorithm arrays reside in one arena. Domain bounds prevent overflow. */
    size_t words=(B+8)*L+E+2,bytes=words*sizeof(limb)+(size_t)r+1+(size_t)span;
    if(cap&&bytes>cap){printf("{\"status\":\"unresolved\",\"required_bytes\":%zu,\"allocated_bytes\":0}\n",bytes);return 3;}
    double start=now();limb *mem=calloc(1,bytes);if(!mem)fail("arena allocation failed",4);
    N=mem;one=N+L;base=one+L;normal=base+L;g=normal+L;h=g+L;t=h+L;limb*xs=t+2*L+2,*e=xs+B*L;unsigned char*small=(unsigned char*)(e+E),*mark=small+r+1;
    if(mark+span!=(unsigned char*)mem+bytes)fail("layout",4);
    parse(N,argv[6],nl);parse(e,argv[7],el);limb v=1;for(int j=0;j<5;j++)v*=2u-N[0]*v;ninv=0u-v;
    if((limb)(N[0]*ninv)!=UINT32_MAX)fail("inverse",4);
    size_t bottom=0,top=4*el-1;while(!bit(e,bottom))bottom++;while(!bit(e,top))top--;
    uint64_t s=1+bottom+ubits(K)-1;setsmall(one,1);tomont(one);
    for(size_t i=0;i<B;i++){limb*x=xs+i*L;setsmall(x,i+2);tomont(x);bigpower(x,e,top,bottom);}
    memset(small,1,r+1);small[0]=0;if(r>=1)small[1]=0;
    for(uint64_t p=2;p<=r/p;p++)if(small[p])for(uint64_t j=p*p;j<=r;j+=p)small[j]=0;
    uint64_t primes=0,segments=0,chunk=1;
    for(uint64_t lo=3;lo<=K;lo+=2*S){uint64_t count=(K-lo)/2+1;if(count>S)count=S;uint64_t hi=lo+2*(count-1);memset(mark,1,count);segments++;
        for(uint64_t p=3;p<=r&&p<=hi/p;p+=2)if(small[p]){uint64_t first=((lo+p-1)/p)*p;if(first<p*p)first=p*p;if(!(first&1))first+=p;for(uint64_t j=(first-lo)/2;j<count;j+=p)mark[j]=0;}
        for(uint64_t j=0;j<count;j++)if(mark[j]){uint64_t p=lo+2*j,q=p;while(q<=K/p)q*=p;primes++;
            if(chunk!=1&&ubits(chunk)+ubits(q)>W){for(size_t i=0;i<B;i++)power(xs+i*L,chunk);chunk=1;}
            if(ubits(q)>W){for(size_t i=0;i<B;i++)power(xs+i*L,q);}else{chunk*=q;if(ubits(chunk)>W)fail("chunk width",4);}
        }
        if(chunk!=1){for(size_t i=0;i<B;i++)power(xs+i*L,chunk);chunk=1;}
    }
    double seconds=now()-start;
    printf("{\"status\":\"ok\",\"required_bytes\":%zu,\"allocated_bytes\":%zu,\"seconds\":%.9f,\"montgomery_multiplications\":%" PRIu64 ",\"pow_calls\":%" PRIu64 ",\"prime_powers\":%" PRIu64 ",\"segments\":%" PRIu64 ",\"s\":%" PRIu64 ",\"residues\":[",bytes,bytes,seconds,muls,pows,primes,segments,s);
    for(size_t i=0;i<B;i++){if(i)putchar(',');unmont(normal,xs+i*L);putchar('"');printhex(normal);putchar('"');}
    printf("],\"splits\":[");
    for(size_t i=0;i<B;i++){if(i)putchar(',');limb*x=xs+i*L;setsmall(normal,i+2);gcdfixed(normal);long index=-2;
        if(!isone(h)&&cmp(h,N)<0)index=-1;
        else for(uint64_t j=0;j<=s;j++){unmont(normal,x);if(zero(normal))setsmall(normal,1);else{limb borrow=1;for(size_t l=0;l<L&&borrow;l++){limb old=normal[l];normal[l]--;borrow=old==0;}}gcdfixed(normal);if(!isone(h)&&cmp(h,N)<0){index=(long)j;break;}if(j<s)mont(x,x,x);}
        if(index==-2)printf("null");else{printf("[%ld,\"",index);printhex(h);printf("\"]");}
    }
    struct rusage ru;getrusage(RUSAGE_SELF,&ru);printf("],\"peak_rss_kib\":%ld}\n",ru.ru_maxrss);free(mem);return 0;
}
