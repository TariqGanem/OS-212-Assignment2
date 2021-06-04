#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"

#define MAX_BSEM 128
struct binary_semaphore semaphores[MAX_BSEM];
extern void* sigret_start(void);
extern void* sigret_end(void);

struct cpu cpus[NCPU];

struct proc proc[NPROC];

struct proc *initproc;

int nextpid = 1;
int nexttid = 1;
struct spinlock pid_lock;
struct spinlock tid_lock;

extern void forkret(void);
static void freeproc(struct proc *p);
static void freethread(struct thread *t);

extern char trampoline[]; // trampoline.S

// helps ensure that wakeups of wait()ing
// parents are not lost. helps obey the
// memory model when using p->parent.
// must be acquired before any p->lock.
struct spinlock wait_lock;

// Allocate a page for each process's kernel stack.
// Map it high in memory, followed by an invalid
// guard page.
void
proc_mapstacks(pagetable_t kpgtbl) {
  struct proc *p;
  
  for(p = proc; p < &proc[NPROC]; p++) {
    char *pa = kalloc();
    if(pa == 0)
      panic("kalloc");
    uint64 va = KSTACK((int) (p - proc));
    kvmmap(kpgtbl, va, (uint64)pa, PGSIZE, PTE_R | PTE_W);
  }
}

// initialize the proc table at boot time.
void
procinit(void)
{
  struct proc *p;
  struct thread *t;
  struct binary_semaphore* b;
  initlock(&tid_lock, "nexttid");
  initlock(&pid_lock, "nextpid");
  initlock(&wait_lock, "wait_lock");
  for(p = proc; p < &proc[NPROC]; p++) {
    initlock(&p->lock, "proc");
    for(t = p->threads; t < &p->threads[NTHREAD]; t++){
      initlock(&t->lock, "thread");
    }
  }
  for(b = semaphores; b < &semaphores[MAX_BSEM]; b++)
    initlock(&b->lock, "binary_semaphore");
}

// Must be called with interrupts disabled,
// to prevent race with process being moved
// to a different CPU.
int
cpuid()
{
  int id = r_tp();
  return id;
}

// Return this CPU's cpu struct.
// Interrupts must be disabled.
struct cpu*
mycpu(void) {
  int id = cpuid();
  struct cpu *c = &cpus[id];
  return c;
}

// Return the current struct proc *, or zero if none.
struct proc*
myproc(void) {
  push_off();
  struct cpu *c = mycpu();
  struct proc *p = c->proc;
  pop_off();
  return p;
}

struct thread*
mythread(void) {
  push_off();
  struct cpu *c = mycpu();
  struct thread *t = c->t;
  pop_off();
  return t;
}

int
allocpid() {
  int pid;
  
  acquire(&pid_lock);
  pid = nextpid;
  nextpid = nextpid + 1;
  release(&pid_lock);

  return pid;
}

int alloctid()
{
  int tid;

  acquire(&tid_lock);
  tid = nexttid;
  nexttid = nexttid + 1;
  release(&tid_lock);

  return tid;
}

static struct thread*
allocthread(struct proc *p)
{
  struct thread *t;
  struct thread *curr_t = mythread();                  
  int index = 0;
  for(t = p->threads; &p->threads[NTHREAD]; t++) {
    if(t != curr_t) {
      acquire(&t->lock);
      if(t->state == TUNUSED) {
        goto found;
      } else {
        release(&t->lock);
      } 
    }
    index++;
  }
  return 0;

found:
  t->index = index;
  t->tid = alloctid();
  t->state = TUSED;
  t->killed = 0;
  t->parent = p;
  t->trapframe = &p->trapframes[index];

  if((t->backupFrame = (struct trapframe *)kalloc()) == 0) {
    freethread(t);
    release(&t->lock);
    return 0;
  }

  if((t->kstack = (uint64)kalloc()) == 0){
    freethread(t);
    release(&t->lock);
    return 0;
  }

  memset(&t->context, 0, sizeof(t->context));
  t->context.ra = (uint64)forkret;
  t->context.sp = t->kstack + PGSIZE;

  return t;
}

// Look in the process table for an UNUSED proc.
// If found, initialize state required to run in the kernel,
// and return with p->lock held.
// If there are no free procs, or a memory allocation fails, return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;

  for(p = proc; p < &proc[NPROC]; p++) {
    acquire(&p->lock);
    if(p->state == UNUSED) {
      goto found;
    } else {
      release(&p->lock);
    }
  }
  return 0;

found:
  p->pid = allocpid();
  p->state = USED;

  // Allocate a trapframe page.
  if((p->trapframes = (struct trapframe *)kalloc()) == 0){
    freeproc(p);
    release(&p->lock);
    return 0;
  }

  // An empty user page table.
  p->pagetable = proc_pagetable(p);
  if(p->pagetable == 0){
    freeproc(p);
    release(&p->lock);
    return 0;
  }

  for(int i = 0; i < 32; i++)
    p->signalHandlers[i] = (void*)SIG_DFL;
  
  struct thread *t = allocthread(p);
  if(t == 0){
    release(&t->lock);          
    freeproc(p);
    release(&p->lock);
    return 0;
  }

  release(&t->lock);

  // Set up new context to start executing at forkret,
  // which returns to user space.
  return p;
}

// free a proc structure and the data hanging from it,
// including user pages.
// p->lock must be held.
static void
freeproc(struct proc *p)
{
  if(p->trapframes)
    kfree((void*)p->trapframes);
  p->trapframes = 0;
  if(p->pagetable)
    proc_freepagetable(p->pagetable, p->sz);
  p->pagetable = 0;
  p->sz = 0;
  p->pid = 0;
  p->parent = 0;
  p->name[0] = 0;
  p->killed = 0;
  p->xstate = 0;
  p->state = UNUSED;
  p->pendingSignals = 0;
  p->sigmask = 0;

  for(int i = 0; i < 32; i++){
    p->signalHandlers[i] = (void*)SIG_DFL;
    p->handlersMasks[i] = 0;
  }

  p->isHandling = 0;
  p->previousMask = 0;

  struct thread *t;
  for(t = p->threads; t < &p->threads[NTHREAD]; t++)
    freethread(t);
}

static void
freethread(struct thread *t)
{
  if(t->backupFrame)
    kfree((void*)t->backupFrame);
  t->backupFrame = 0;
  if(t->kstack)
    kfree((void*)t->kstack);
  t->kstack = 0;
  t->trapframe = 0;
  t->chan = 0;
  t->index = 0;
  t->xstate = 0;
  t->tid = 0;
  t->parent = 0;
  t->killed = 0;
  t->state = TUNUSED;
}

// Create a user page table for a given process,
// with no user memory, but with trampoline pages.
pagetable_t
proc_pagetable(struct proc *p)
{
  pagetable_t pagetable;

  // An empty page table.
  pagetable = uvmcreate();
  if(pagetable == 0)
    return 0;

  // map the trampoline code (for system call return)
  // at the highest user virtual address.
  // only the supervisor uses it, on the way
  // to/from user space, so not PTE_U.
  if(mappages(pagetable, TRAMPOLINE, PGSIZE,
              (uint64)trampoline, PTE_R | PTE_X) < 0){
    uvmfree(pagetable, 0);
    return 0;
  }

  // map the trapframe just below TRAMPOLINE, for trampoline.S.
  if(mappages(pagetable, TRAPFRAME(0), PGSIZE,
              (uint64)(p->trapframes), PTE_R | PTE_W) < 0){
    uvmunmap(pagetable, TRAMPOLINE, 1, 0);
    uvmfree(pagetable, 0);
    return 0;
  }

  return pagetable;
}

// Free a process's page table, and free the
// physical memory it refers to.
void
proc_freepagetable(pagetable_t pagetable, uint64 sz)
{
  uvmunmap(pagetable, TRAMPOLINE, 1, 0);
  uvmunmap(pagetable, TRAPFRAME(0), 1, 0);
  uvmfree(pagetable, sz);
}

// a user program that calls exec("/init")
// od -t xC initcode
uchar initcode[] = {
  0x17, 0x05, 0x00, 0x00, 0x13, 0x05, 0x45, 0x02,
  0x97, 0x05, 0x00, 0x00, 0x93, 0x85, 0x35, 0x02,
  0x93, 0x08, 0x70, 0x00, 0x73, 0x00, 0x00, 0x00,
  0x93, 0x08, 0x20, 0x00, 0x73, 0x00, 0x00, 0x00,
  0xef, 0xf0, 0x9f, 0xff, 0x2f, 0x69, 0x6e, 0x69,
  0x74, 0x00, 0x00, 0x24, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00
};

// Set up first user process.
void
userinit(void)
{
  struct proc *p;

  p = allocproc();
  initproc = p;
  
  // allocate one user page and copy init's instructions
  // and data into it.
  uvminit(p->pagetable, initcode, sizeof(initcode));
  p->sz = PGSIZE;

  // prepare for the very first "return" from kernel to user.
  p->trapframes->epc = 0;      // user program counter
  p->trapframes->sp = PGSIZE;  // user stack pointer

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  p->threads[0].state = TRUNNABLE;

  release(&p->lock); 
}

// Grow or shrink user memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *p = myproc();
  acquire(&p->lock);
  sz = p->sz;
  if(n > 0){
    if((sz = uvmalloc(p->pagetable, sz, sz + n)) == 0) {
      release(&p->lock);
      return -1;
    }
  } else if(n < 0){
    sz = uvmdealloc(p->pagetable, sz, sz + n);
  }
  p->sz = sz;
  release(&p->lock);
  return 0;
}

// Create a new process, copying the parent.
// Sets up child kernel stack to return as if from fork() system call.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct thread *nt;
  struct proc *p = myproc();
  struct thread *curr_t = mythread();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }
  
  // Copy user memory from parent to child.
  if(uvmcopy(p->pagetable, np->pagetable, p->sz) < 0){
    freeproc(np);
    release(&np->lock);
    return -1;
  }
  np->sz = p->sz;
  nt = &np->threads[0];
  *nt->trapframe = *curr_t->trapframe;

  // Cause fork to return 0 in the child.
  nt->trapframe->a0 = 0;

  // increment reference counts on open file descriptors.
  for(i = 0; i < NOFILE; i++)
    if(p->ofile[i])
      np->ofile[i] = filedup(p->ofile[i]);
  np->cwd = idup(p->cwd);

  safestrcpy(np->name, p->name, sizeof(p->name));

  pid = np->pid;
  // When fork is used, parent's signal mask and signal handlers will be inherited but not pending signals
  np->sigmask = p->sigmask;
  for(int i = 0; i < 32; i++){
    np->signalHandlers[i] = p->signalHandlers[i];
    np->handlersMasks[i] = p->handlersMasks[i];
  }
  np->pendingSignals = 0;

  release(&np->lock);

  acquire(&wait_lock);
  np->parent = p;
  release(&wait_lock);

  acquire(&nt->lock);
  nt->state = TRUNNABLE;
  release(&nt->lock);

  return pid;
}

// Pass p's abandoned children to init.
// Caller must hold wait_lock.
void
reparent(struct proc *p)
{
  struct proc *pp;

  for(pp = proc; pp < &proc[NPROC]; pp++){
    if(pp->parent == p){
      pp->parent = initproc;
      wakeup(initproc);
    }
  }
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait().
void
exit(int status)
{
  struct proc *p = myproc();
  struct thread *curr_t = mythread();

  if(p == initproc)
    panic("init exiting");

  // Close all open files.
  for(int fd = 0; fd < NOFILE; fd++){
    if(p->ofile[fd]){
      struct file *f = p->ofile[fd];
      fileclose(f);
      p->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(p->cwd);
  end_op();
  p->cwd = 0;

  acquire(&wait_lock);

  // Give any children to init.
  reparent(p);

  // Parent might be sleeping in wait().
  wakeup(p->parent);
  
  acquire(&p->lock);

  p->xstate = status;
  p->state = ZOMBIE;

  struct thread *t;
  for(t = p->threads; t < &p->threads[NTHREAD]; t++){
    if(t != curr_t && t->state != TUNUSED){
      acquire(&t->lock);
      t->killed = 1;
      if(t->state == TSLEEPING)
        t->state = TRUNNABLE;
      release(&t->lock);
      // waiting for thread to be killed
      kthread_join(t->tid, 0);
    }
  }
  release(&p->lock);
  acquire(&curr_t->lock);
  curr_t->state = TZOMBIE;

  release(&wait_lock);

  // Jump into the scheduler, never to return.
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(uint64 addr)
{
  struct proc *np;
  int havekids, pid;
  struct proc *p = myproc();

  acquire(&wait_lock);

  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(np = proc; np < &proc[NPROC]; np++){
      if(np->parent == p){
        // make sure the child isn't still in exit() or swtch().
        acquire(&np->lock);

        havekids = 1;
        if(np->state == ZOMBIE){
          // Found one.
          pid = np->pid;
          if(addr != 0 && copyout(p->pagetable, addr, (char *)&np->xstate,
                                  sizeof(np->xstate)) < 0) {
            release(&np->lock);
            release(&wait_lock);
            return -1;
          }
          freeproc(np);
          release(&np->lock);
          release(&wait_lock);
          return pid;
        }
        release(&np->lock);
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || p->killed){
      release(&wait_lock);
      return -1;
    }
    
    // Wait for a child to exit.
    sleep(p, &wait_lock);  //DOC: wait-sleep
  }
}

// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run.
//  - swtch to start running that process.
//  - eventually that process transfers control
//    via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  struct thread *t;
  struct cpu *c = mycpu();
  
  c->proc = 0;
  c->t = 0;
  for(;;){
    // Avoid deadlock by ensuring that devices can interrupt.
    intr_on();

    for(p = proc; p < &proc[NPROC]; p++) {
      if(p->state == USED){
        for(t = p->threads; t < &p->threads[NTHREAD]; t++){
          acquire(&t->lock);
          if(t->state == TRUNNABLE){
            c->proc = p;
            c->t = t;
            t->state = TRUNNING;
            swtch(&c->context, &t->context);
            c->proc = 0;
            c->t = 0;
          }
          release(&t->lock);
        }
      }
    }
  }
}

// Switch to scheduler.  Must hold only p->lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->noff, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct thread *t = mythread();
  if(!holding(&t->lock)) 
    panic("sched p->lock");
  if(mycpu()->noff != 1)
    panic("sched locks");
  if(t->state == TRUNNING)
    panic("sched running");
  if(intr_get())
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&t->context, &mycpu()->context);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  struct thread *t = mythread();
  acquire(&t->lock);
  t->state = TRUNNABLE;
  sched();
  release(&t->lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch to forkret.
void
forkret(void)
{
  static int first = 1;

  // Still holding p->lock from scheduler.
  release(&mythread()->lock);

  if (first) {
    // File system initialization must be run in the context of a
    // regular process (e.g., because it calls sleep), and thus cannot
    // be run from main().
    first = 0;
    fsinit(ROOTDEV);
  }

  usertrapret();
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct thread *t = mythread();
  
  // Must acquire p->lock in order to
  // change p->state and then call sched.
  // Once we hold p->lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup locks p->lock),
  // so it's okay to release lk.

  acquire(&t->lock);  //DOC: sleeplock1
  release(lk);

  // Go to sleep.
  t->chan = chan;
  t->state = TSLEEPING;

  sched();

  // Tidy up.
  t->chan = 0;

  // Reacquire original lock.
  release(&t->lock);
  acquire(lk);
}

// Wake up all processes sleeping on chan.
// Must be called without any p->lock.
void
wakeup(void *chan)
{
  struct proc *p;
  struct thread *t;
  struct thread *curr_t = mythread();

  for(p = proc; p < &proc[NPROC]; p++) {
    for(t = p->threads; t < &p->threads[NTHREAD]; t++){
      if(t != curr_t){ 
        acquire(&t->lock);
        if(t->state == TSLEEPING && t->chan == chan) {
          t->state = TRUNNABLE;
        }
        release(&t->lock);
      }
    }
  }
}

// Kill the process with the given pid.
// The victim won't exit until it tries to return
// to user space (see usertrap() in trap.c).
int
kill(int pid, int signum)
{
  struct proc *p;
  for(p = proc; p < &proc[NPROC]; p++){
    acquire(&p->lock);
    if(p->pid == pid){
      if(p->state != USED){
        release(&p->lock);
        return -1;
      }
      p->pendingSignals = (p->pendingSignals | (1 << signum));
      release(&p->lock);
      return 0;
    }
    release(&p->lock);
  }
  return -1;
}

// Copy to either a user address, or kernel address,
// depending on usr_dst.
// Returns 0 on success, -1 on error.
int
either_copyout(int user_dst, uint64 dst, void *src, uint64 len)
{
  struct proc *p = myproc();
  if(user_dst){
    return copyout(p->pagetable, dst, src, len);
  } else {
    memmove((char *)dst, src, len);
    return 0;
  }
}

// Copy from either a user address, or kernel address,
// depending on usr_src.
// Returns 0 on success, -1 on error.
int
either_copyin(void *dst, int user_src, uint64 src, uint64 len)
{
  struct proc *p = myproc();
  if(user_src){
    return copyin(p->pagetable, dst, src, len);
  } else {
    memmove(dst, (char*)src, len);
    return 0;
  }
}

// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [ZOMBIE]    "zombie"
  };
  struct proc *p;
  char *state;

  printf("\n");
  for(p = proc; p < &proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    printf("%d %s %s", p->pid, state, p->name);
    printf("\n");
  }
}

uint
sigprocmask(uint sigmask)
{
  if(sigmask != SIGKILL && sigmask != SIGSTOP){
    struct proc *p = myproc();
    acquire(&p->lock);
    uint oldMask = p->sigmask;
    p->sigmask = sigmask;
    release(&p->lock);
    return oldMask;
  } else{
    return -1;
  }
}

int
updateHandler(struct proc *p, uint64 act, int signum)
{
  struct sigaction tmp;
  int isOk = 1;
  if(act){
    if((copyin(p->pagetable, (char*)&tmp, act, sizeof(struct sigaction)) >= 0)){
      if((((1 << SIGKILL) & tmp.sigmask) != 0) || (((1 << SIGSTOP) & tmp.sigmask) != 0)) {
        release(&p->lock);
        isOk = 0;
      } else {
        p->signalHandlers[signum] = tmp.sa_handler;
        p->handlersMasks[signum] = tmp.sigmask;
      }
    }
  }
  return isOk;
}

int
sigaction(int signum, uint64 act, uint64 oldact)
{
  struct proc *p = myproc();
  // We shouldn't change the default handler for SIGDFL and SIGKILL
  if(signum < 0 || signum > 31 || signum == SIGKILL || signum == SIGSTOP)
    return -1;
  acquire(&p->lock);
  // If oldcat is non-NULL then save the previous action in oldact
  if(oldact){
    copyout(p->pagetable, oldact, (char*)&p->signalHandlers[signum], sizeof(p->signalHandlers[signum]));  // copy the handler
    copyout(p->pagetable, oldact + sizeof(p->signalHandlers[signum]), (char*)&p->handlersMasks[signum], sizeof(uint));  // copy the specific sigmask
  }
  if(!updateHandler(p, act, signum))
    return -1;
  release(&p->lock);
  return 0;
}

// Restoring the process original workflow
void
sigret(void)
{
  struct proc *p = myproc();
  struct thread *t = mythread();
  acquire(&p->lock);
  acquire(&t->lock);
  memmove(t->trapframe, t->backupFrame, sizeof(struct trapframe));
  p->sigmask = p->previousMask;
  p->isHandling = 0;
  release(&t->lock);
  release(&p->lock);
}

void
sigkill()
{
  struct proc *p = myproc();
  struct thread *t;
  p->killed = 1;
  for(t = p->threads; t < &p->threads[NTHREAD]; t++) {
    acquire(&t->lock);
    if(t->state == TSLEEPING){
      t->state = TRUNNABLE;
    }
    release(&t->lock);
  }  
}

void
sigcont()
{
  struct proc *p = myproc();
  if (((1 << SIGSTOP) & p->pendingSignals) == 0)
    p->pendingSignals = p->pendingSignals & ~(1 << SIGCONT);
}

void
sigstop()
{
  struct proc *p = myproc();
  while(1){
    if (!holding(&p->lock))
      acquire(&p->lock);
    if (!(p->pendingSignals & (1 << SIGCONT))){
      release(&p->lock);
      yield();
    } else {
      break;
    }
  }
  p->pendingSignals = p->pendingSignals & ~(1 << SIGSTOP);
  p->pendingSignals = p->pendingSignals & ~(1 << SIGCONT);
}

void
checkAndExecute(struct proc *p, int i, uint currSig)
{
  switch(i){
    case SIGKILL:
      sigkill();
      p->pendingSignals = p->pendingSignals & ~currSig;
      break;
    case SIGSTOP:
      sigstop();
      break;
    case SIGCONT:
      sigcont();
      break;
    default:
      sigkill();
      p->pendingSignals = p->pendingSignals & ~currSig;
      break;
  }
}

void 
notSIG_DFL(struct proc *p, int i, uint currSig)
{
  struct thread *t = mythread();
  p->previousMask = p->sigmask;
  p->sigmask = p->handlersMasks[i];
  p->isHandling = 1;
  memmove(t->backupFrame, t->trapframe, sizeof(struct trapframe));
  uint sigret_size = sigret_end - sigret_start;
  t->trapframe->sp -= sigret_size;
  copyout(p->pagetable, (uint64)t->trapframe->sp, (char*)&sigret_start, sigret_size);
  t->trapframe->a0 = i;
  t->trapframe->ra = t->trapframe->sp;
  p->pendingSignals = p->pendingSignals & ~currSig;
  t->trapframe->epc = (uint64)p->signalHandlers[i];
}

void
handleSignals()
{
  struct proc *p = myproc();
  acquire(&p->lock);
  if (p->isHandling){ 
    release(&p->lock);
    return;
  }
  for(int i = 0; i < 32; i++){
    uint currSig = 1 << i;
    if((currSig & p->pendingSignals) && !(currSig & p->sigmask)){
      if (p->signalHandlers[i] == (void*)SIG_IGN) {
        p->pendingSignals = p->pendingSignals & ~currSig;
        continue;
      }
      if (p->signalHandlers[i] == (void*)SIG_DFL){
        checkAndExecute(p, i, currSig);
      }
      else { 
        notSIG_DFL(p, i, currSig);
      }
    }
  }
  release(&p->lock);
}

int
kthread_create(uint64 start_func, uint64 stack)
{
  int tid;
  struct proc *p = myproc();
  struct thread *t = mythread();
  struct thread *nt = nt = allocthread(p);

  if(nt != 0) {
    tid = nt->tid;
    nt->state = TRUNNABLE;
    *nt->trapframe = *t->trapframe;
    nt->trapframe->epc = (uint64)start_func;
    nt->trapframe->sp = (uint64)(stack + MAX_STACK_SIZE - 16);
    release(&nt->lock);
    return tid;
  }
  return -1;
}

int
kthread_id()
{
  struct thread *t = mythread();
  if(t == 0)
    return -1;
  return t->tid;
}

void kthread_exit(int status)
{
  struct proc *p = myproc();
  struct thread *curr_t = mythread();
  struct thread *t;

  acquire(&p->lock);
  int numOfThreads = 0;
  for(t = p->threads; t < &p->threads[NTHREAD]; t++){
    acquire(&t->lock);
    if(t != curr_t && t->state != TUNUSED && t->state != TZOMBIE)
      numOfThreads++;
    release(&t->lock);
  }
  if (numOfThreads == 0) {
    release(&p->lock);
    exit(status);
  }

  acquire(&curr_t->lock);
  curr_t->xstate = status;
  curr_t->state = TZOMBIE;

  release(&p->lock);
  
  wakeup(curr_t);
  
  sched();
}

int
kthread_join(int thread_id, int *status)
{
  struct thread *toJoinThread;
  struct proc *p = myproc();
  struct thread *t;

  for(t = p->threads; t < &p->threads[NTHREAD]; t++) {
    acquire(&t->lock);
    if(thread_id == t->tid) {
      toJoinThread = t;
      goto found;
    }
    release(&t->lock);
  }

  return -1;

  found:
    while (toJoinThread->state != TZOMBIE && toJoinThread->state != TUNUSED)  // waiting for the thread to finish its running
      sleep(toJoinThread, &toJoinThread->lock);

    if(toJoinThread->state == TZOMBIE){ // which means the thread finished his running
      if(status != 0 && copyout(p->pagetable, (uint64)status, (char *)&toJoinThread->xstate, sizeof(toJoinThread->xstate)) < 0) {
        release(&toJoinThread->lock);
        return -1;
      }
      freethread(toJoinThread);
    } 

    release(&toJoinThread->lock);
    return 0;
}

int bsem_alloc()
{
  int d;
  int isOk = 0;
  for(d = 0; d < MAX_BSEM && !isOk; d++){
    acquire(&semaphores[d].lock);
    if(!semaphores[d].isTaken){
      isOk = 1;
      break;
    }
    release(&semaphores[d].lock);
  }
  if(isOk){
    semaphores[d].isTaken = 1;
    semaphores[d].val = 1;    
    release(&semaphores[d].lock);
    return d;
  }
  return -1;
}

void bsem_free(int d)
{
  acquire(&semaphores[d].lock);
  semaphores[d].isTaken = 0;
  release(&semaphores[d].lock);
}

void bsem_down(int d)
{
  acquire(&semaphores[d].lock);
  if(semaphores[d].isTaken) {
    while(semaphores[d].val == 0)
      sleep(&semaphores[d], &semaphores[d].lock);
    semaphores[d].val = 0;
  }
  release(&semaphores[d].lock);
}

void bsem_up(int d)
{
  acquire(&semaphores[d].lock);
  if(semaphores[d].isTaken) {
    semaphores[d].val = 1;
    wakeup(&semaphores[d]);
  }
  release(&semaphores[d].lock);
}