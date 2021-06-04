struct counting_semaphore {
    int val;
    int sema_1;
    int sema_2;
};

void csem_down(struct counting_semaphore *sem);
void csem_up(struct counting_semaphore *sem);
int csem_alloc(struct counting_semaphore *sem, int initial_value);
void csem_free(struct counting_semaphore *sem);