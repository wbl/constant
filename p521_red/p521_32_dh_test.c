#include<fcntl.h>
#include<stdio.h>
#include<unistd.h>
#include<stdbool.h>
#include "p521_32.h"


int main(){
  unsigned char ask[66];
  unsigned char bsk[66];
  unsigned char A[132];
  unsigned char B[132];
  unsigned char KAB[132];
  unsigned char KBA[132];
  int fd = open("/dev/urandom", O_RDONLY);
  for(int i=0; i<10; i++){
    read(fd, ask, 66);
    read(fd, bsk, 66);
    ask[65]=0;
    bsk[65]=0;
    p521_32_scalarmult_base(A, ask);
    p521_32_scalarmult_base(B, bsk);
    p521_32_scalarmult(KAB, bsk, A);
    p521_32_scalarmult(KBA, ask, B);
    int flag = 0;
    for(int i=0; i<132; i++){
      flag |= KAB[i]^KBA[i];
    }
    if(flag){
      printf("DH failure\n");
    }
  }
}
