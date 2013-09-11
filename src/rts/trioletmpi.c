
#ifdef USE_MPI

#include <inttypes.h>
#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

#include "trioletmpi.h"

//#define CHATTY_MPI

// Called from any rank to send/receive a message
static void MPIMessage_initalize(MPIMessage *msg);
static void MPIMessage_finalize(MPIMessage *msg);
static void MPIMessage_send(int dst_rank, const MPIMessage *msg);
static void MPIMessage_recv(int src_rank, MPIMessage *msg);


// Called from rank 0
static void assertRank0(void);
static int getIdleProcess(void);
static void markProcessIdle(int);
static void onTermination(void);

// Called from ranks other than 0
static void slaveProcess(int rank);

#define WORK_TAG 1 // work tag for MPI_Send and MPI_Recv

static int numProcs; // number of processors in the system

// A global lock on static information about the thread pool.
// Protects 'is_busy' and 'thread_state'
static pthread_mutex_t thread_pool_lock = PTHREAD_MUTEX_INITIALIZER;

// Array of length 'numProcs'.  Only used by rank 0.
// is_busy[i] is zero iff node i+1 is idle.
static int *is_busy;

// State of this distributed task
// FIXME: This should be part of a thread-state object, but the infrastructure
// for managing thread state objects isn't there
ThreadState thread_state = {0};


///////////////////////////////////////////////////////////////////////////////

static void
MPIMessage_initalize(MPIMessage *msg)
{
  msg->length = 0;
  msg->data = NULL;
}

static void
MPIMessage_finalize(MPIMessage *msg)
{
  free(msg->data);
  msg->length = 0;
  msg->data = NULL;
}

static void
MPIMessage_send(int dst_rank, const MPIMessage *msg)
{
  char *data = msg->data;        // data buffer
  int length = msg->length;      // length of the data buffer
  MPI_Send(&length, 1, MPI_INT, dst_rank, WORK_TAG, MPI_COMM_WORLD);

  if (length) {
    MPI_Send(data, length, MPI_CHARACTER, dst_rank, WORK_TAG, MPI_COMM_WORLD);
  }
}

static void
MPIMessage_recv(int src_rank, MPIMessage *msg)
{
  char *data;                   // data buffer
  int length;                   // length of buffer
  MPI_Recv(&length, 1, MPI_INT, src_rank,
           WORK_TAG, MPI_COMM_WORLD, MPI_STATUS_IGNORE);

  if (length != 0) {
    data = (char*)malloc(length * sizeof(char));
    MPI_Recv(data, length, MPI_CHARACTER, src_rank,
             WORK_TAG, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  }
  else {
    data = NULL;
  }
  msg->length = length;
  msg->data = data;
}

static void
assertRank0(void)
{
  int rank;
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);
  if (rank != 0) {
    fprintf(stderr,
            "Worker performed an action that is only permitted on the main process\n");
    exit(-1);
  }
}

// Called from rank 0.
// Find the rank of a slave that is not currently busy.
static int
getIdleProcess(void) {
  int i;
  pthread_mutex_lock(&thread_pool_lock);

  // Search for an idle slave
  for(i=0;i<numProcs-1;i++) {
    if(!is_busy[i]) {
      is_busy[i] = 1;
      goto done;
    }
  }
  // No idle slaves
  fprintf(stderr, "Scheduling problem: no idle MPI processes available\n");
  exit(-1);

 done:
  pthread_mutex_unlock(&thread_pool_lock);
  return i+1;
}

// Record the fact that a rank is idle
static void
markProcessIdle(int rank) {
  pthread_mutex_lock(&thread_pool_lock);
  is_busy[rank-1] = 0;
  pthread_mutex_unlock(&thread_pool_lock);
}

// Called when rank 0 exits.
static void onTermination(void) {
  MPIMessage msg = {0, ""};
  int i;

#ifdef CHATTY_MPI
  printf("Sending termination messages\n");
#endif

  // Notify all slaves that the main process is exiting
  for(i=0;i<numProcs-1;i++)
    MPIMessage_send(i+1, &msg);

  // Finalize MPI layer
  MPI_Finalize();
}

static void
slaveProcess_sendResult(int32_t length, char *data);

// Run a slave process
static void
slaveProcess(int rank) {
  struct timeval t1, t2, t3;
  while(1) {
    // Receive a command from rank 0
    MPIMessage command;
    MPIMessage_recv(0, &command);

    if (command.length == 0) {
      // Termination message
#ifdef CHATTY_MPI
      printf("Rank %d received termination message\n", rank);
#endif
      MPIMessage_finalize(&command);
      break;
    }
#ifdef CHATTY_MPI
    printf("Rank %d received data\n", rank);
#endif

    // Run the command
    MPIMessage output;
    triolet_begin_distributed_task();
    triolet_run_task(command.length, command.data, &slaveProcess_sendResult);
    triolet_end_distributed_task();
    MPIMessage_finalize(&command);
  }

  // Finalize MPI layer
  MPI_Finalize();

  // End the program
  exit(0);
}

// Called on the output of a slave task.  Send it to rank 0.
static void
slaveProcess_sendResult(int32_t length, char *data)
{
  // Send the result back to rank 0
  MPIMessage m = {length, data};
  MPIMessage_send(0, &m);
}

// Launch the MPI task interface.
// If MPI rank is zero, then return.
// If MPI rank is not zero, then run a loop that waits for MPI messages.
int triolet_MPITask_setup(int *argc, char ***argv) {
  int thread_support_provided;
  MPI_Init_thread(argc, argv, MPI_THREAD_SINGLE, &thread_support_provided);

  MPI_Comm_size(MPI_COMM_WORLD, &numProcs);
  int rank;
  MPI_Comm_rank(MPI_COMM_WORLD, &rank);

#ifdef CHATTY_MPI
  printf("Starting MPI on rank %d\n", rank);
#endif

  if(rank == 0) {
    is_busy = (int *)malloc((numProcs-1)*sizeof(int));
    int i;
    /* All slaves are initially idle */
    for(i=0;i<numProcs-1;i++)
      is_busy[i] = 0;

    /* Notify slaves when the main process exits */
    atexit(&onTermination);

    return 0;
  }
  else {
    slaveProcess(rank);
  }
  // Unreachable
  return -1;
}

// This function can only be called from rank 0.
// Launch some work on an idle process.  Error if there are no idle processes.
MPITask triolet_MPITask_launch(int length, char *data) {
  // Correctness checks
  assertRank0();
  if (triolet_in_distributed_task()) {
    fprintf(stderr, "Cannot launch a nested distributed task\n");
    exit(-1);
  }

  int dst = getIdleProcess();
  if (dst == -1) {
    fprintf(stderr, "No idle processes\n");
    exit(-1);
  }

  if (length == 0) {
    fprintf(stderr, "Empty message\n");
    exit(-1);
  }

  // Send message to worker
  {
    MPIMessage m = {length, data};
#ifdef CHATTY_MPI
    printf("Launched task on rank %d; size %d\n", dst, length);
#endif
    MPIMessage_send(dst, &m);
  }

  // Construct MPITask object to describe the running task
  MPITask task;
  task = malloc(sizeof(*task));
  task->rank = dst;
  return task;
}

// This function can only be called from rank 0.
// Wait for some work to finish.
// Deallocate the task object.
void *
triolet_MPITask_wait(MPITask task) {
  assertRank0();

  // Wait and get the result of the task
  MPIMessage output;
  MPIMessage_recv(task->rank, &output);
#ifdef CHATTY_MPI
  printf("MPITask_wait: count=%d\n", output.length);
#endif

  // The slave is now idle
  markProcessIdle(task->rank);

  // Construct the result
  void *ret = triolet_deserialize(output.length, output.data);

  // Clean up
  MPIMessage_finalize(&output);
  free(task);
  return ret;
}

void triolet_begin_distributed_task(void)
{
  if (triolet_in_distributed_task()) {
    fprintf(stderr, "Cannot launch a nested distributed task\n");
    exit(-1);
  }
  thread_state.runningDistributedTask = 1;
}

void triolet_end_distributed_task(void)
{
  if (!triolet_in_distributed_task()) {
    fprintf(stderr, "Not running a nested distributed task\n");
    exit(-1);
  }
  thread_state.runningDistributedTask = 0;
}

// Called from Triolet code
int32_t triolet_get_num_distributed_places(void)
{
  return numProcs;
}

// Called from Triolet code
int32_t triolet_in_distributed_task(void)
{
  // Return a boolean (1 -> True; 0 -> False)
  return thread_state.runningDistributedTask;
}


#endif  /* USE_MPI */
