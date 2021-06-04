#include "Csemaphore.h"
#include "kernel/types.h"
#include "user/user.h"
#include "kernel/fcntl.h"

void csem_down(struct counting_semaphore *sem) {
    bsem_down(sem->sema_2);
    bsem_down(sem->sema_1);
    sem->val--;
    if (sem->val > 0)
        bsem_up(sem->sema_2);
    bsem_up(sem->sema_1);
}

void csem_up(struct counting_semaphore *sem) {

    bsem_down(sem->sema_1);
    sem->val++;
    if(sem->val == 1) 
        bsem_up(sem->sema_2);
    bsem_up(sem->sema_1);
}

int csem_alloc(struct counting_semaphore *sem, int initial_value){
    if((initial_value >= 0) && ((sem->sema_1 = bsem_alloc()) >= 0) && ((sem->sema_2 = bsem_alloc()) >= 0)){
        if(initial_value == 0)
            bsem_down(sem->sema_2);
        sem->val = initial_value;
        return 0;
    }
    return -1; // There are no enough binary semaphores which is available  
}

void csem_free(struct counting_semaphore *sem) {
    bsem_free(sem->sema_1);
    bsem_free(sem->sema_2);
}