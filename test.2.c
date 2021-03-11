#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

extern uint64_t test(uint64_t array);

int main() {

    int number;

    uint64_t* array = (uint64_t*) calloc(3, sizeof(uint64_t));
    if(array == NULL) {
        printf("Error while allocating memory for array");
    }

    array[0] = (uint64_t) 5;
    array[1] = (uint64_t) 6;
    array[2] = (uint64_t) 7;

    //uint64_t array[3] = {5,6,7};

	number = (int) test(array);
    printf("%d\n", number);
    
    // Free memory
    free(array);
}