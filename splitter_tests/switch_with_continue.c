#include <stdio.h>

int main(int argvc, char* argv[]) {
  int i;
  for (i=0; i<4; i++) {
    switch(1) {
      case 0:
      case 2:
        printf("EVEN\n");
        break;
      case 1:
      case 3:
        continue;
        printf("ODD WHAT\n");
        break;
    }
  }
}
