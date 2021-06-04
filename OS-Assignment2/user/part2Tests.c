#include "kernel/param.h"
#include "kernel/types.h"
#include "kernel/stat.h"
#include "user/user.h"
#include "kernel/fs.h"
#include "kernel/fcntl.h"
#include "kernel/syscall.h"
#include "kernel/memlayout.h"
#include "kernel/riscv.h"

struct sigaction {
  void (*sa_handler) (int);
  uint sigmask;
};

void test_handler(){
    printf("Handling here - chaning signal handler workd!\n");
}

void init(){
    return;
}

// Unusual cases were checked here
int
test_sigaction_1()
{
    int isOk = 1;
    struct sigaction *act = malloc(sizeof(struct sigaction*));
    if(sigaction(-1, act, 0) != -1){
        printf("test1 failed - signum must be in range 0 -> 31\n");
        isOk = 0;
    }
    if(sigaction(32, act, 0) != -1){
        printf("test1 failed - signum must be in range 0 -> 31\n");
        isOk = 0;
    }
    if(sigaction(SIGSTOP, act, 0) != -1){
        printf("test1 failed - SIGSTOP was found\n");
        isOk = 0;
    }
    if(sigaction(SIGKILL, act, 0) != -1){
        printf("test1 failed - SIGKILL was found\n");
        isOk = 0;
    }
    act->sigmask = (1 << SIGKILL);
    if(sigaction(1, act, 0) == -1){
        act->sigmask = (1 << SIGSTOP);
        if(sigaction(1, act, 0) != -1){
            isOk = 0;
            printf("test1 faild - the act sigmask is SIGSTOP\n");
        }
    } else {
        isOk = 0;
        printf("test1 faild - the act sigmask is SIGKILL\n");
    }
    return isOk; 
}

// Mask update is checked here
int
test_sigaction_2()
{
    int isOK = 1;
    struct sigaction *act = malloc(sizeof(struct sigaction*));
    struct sigaction *temp = malloc(sizeof(struct sigaction*));
    act->sa_handler = &test_handler;
    act->sigmask = 1;
    if(sigaction(1, act, 0) == -1){
        isOK = 0;
        printf("test2 failed - sigaction system call\n");
    }
    sigaction(1, 0, temp);
    if(temp->sigmask != 1){
        isOK = 0;
        printf("test2 failed - the sigmask didn't changed successfully\n");
    }
    return isOK;
}

// Changing handler and using kill syscall
int
test_changeHandler_3()
{
    printf("", &init);
    int isOK = 1;
    struct sigaction *act = malloc(sizeof(struct sigaction*));
    act->sa_handler = &test_handler;
    act->sigmask = 0;
    if(sigaction(1, act, 0) == -1){
        isOK = 0;
        printf("test3 failed - error in sigaction\n");
    }
    int pid = fork();
    if(pid == 0){
        kill(getpid(), 1);
        exit(0);
    } else {
        wait(0);
    }
    return isOK;
}

// sigprocmask was checked
int
test_sigprocmask_4()
{
    int isOk = 1;
    uint prev;
    prev = 0;
    uint mask1 = sigprocmask((1 << 2)); // by default it will be zero
    if(mask1 != prev){
        printf("test4 failed - return value of sigprocmask is invalid\n");
        isOk = 0;
    }
    prev = (1 << 2);
    uint mask2 = sigprocmask((1 << 3));
    if(mask2 != prev){
        printf("test4 failed - return value of sigprocmask is invalid\n");
        isOk = 0;
    }
    return isOk;
}

int main(int argc, char**argv)
{
    int status1 = test_sigaction_1();
    if(status1)
        printf("sigaction unusual cases checked - OK\n");
    else
        printf("sigaction unusual cases checked - FAILED\n");
    int status2 = test_sigaction_2();
    if(status2)
        printf("mask update cases checked - OK\n");
    else
        printf("mask update cases checked - FAILED\n");
    int status3 = test_changeHandler_3();
    if(status3)
        printf("changing default handler checked - OK\n");
    else
        printf("changing default handler checked - FAILED\n");
    int status4 = test_sigprocmask_4();
    if(status4)
        printf("sigprocmask checked - OK\n");
    else
        printf("sigprocmask checked - FAILED\n");
    if(status1 && status2 && status3 && status4)
        printf("ALL TESTS PASSED!\n");
    exit(0);
}
