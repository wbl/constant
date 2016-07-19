#include<fcntl.h>
#include<stdio.h>
#include<unistd.h>
#include<stdbool.h>
#include "p521_64.h"

int main(){
  unsigned char a[66];
  unsigned char A[132];
  for(int i=0; i<66; i++){
    a[i] = 0;
  }
  for(int i=0; i<132; i++){
    A[i] = 0;
  }
  for(int i=1; i<20; i++){
    a[0]=i;
    p521_64_scalarmult_base(A, a);
    printf("k = %d\nx = ", i);
    for(int i=0; i<66; i++){
      printf("%02x", A[i]);
    }
    printf("\ny = ");
    for(int i=0; i<66; i++){
      printf("%02x", A[66+i]);
    }
    printf("\n\n");
  }
}
