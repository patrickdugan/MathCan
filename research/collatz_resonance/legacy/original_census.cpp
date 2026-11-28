#include <cstdio>
#include <cstdint>
#include <vector>
#include <numeric>
#include <algorithm>
int main(){const uint32_t d=160833217,N=(d+1)/2;std::vector<uint8_t> st(N);auto step=[&](uint32_t i){uint32_t n=2*i+1;uint32_t y=((n&3)==1?3*n:n)+d;return ((y>>__builtin_ctz(y))-1)/2;};for(uint32_t i=0;i<N;i++){if(st[i])continue;uint32_t j=i;while(!st[j]){st[j]=1;j=step(j);}if(st[j]==1){uint32_t k=j,m=2*j+1,r=0,A=0,u=0;do{uint32_t n=2*k+1;bool b=(n&3)==1;uint32_t y=(b?3*n:n)+d;unsigned a=__builtin_ctz(y);m=std::min(m,n);++r;A+=a;u+=b;k=((y>>a)-1)/2;}while(k!=j);printf("%u,%u,%u,%u,%u\n",m,r,A,u,std::gcd(m,d));}j=i;while(st[j]==1){st[j]=2;j=step(j);}}}
