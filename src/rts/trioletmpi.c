
#ifdef USE_MPI

#include <inttypes.h>
#include <mpi.h>
#include <stdio.h>
#include <stdlib.h>

#include "trioletmpi.h"

//#define CHATTY_MPI

// Called from any rank to send/receive a message
static void MPIMessage_initalize(MPIMessage *msg);
static void MPIMessage_finalize(MPIMessage *msg);
static void MPIMessage_send(int dst_rank, const MPIMessage *msg);
static void MPIMessage_recv(int src_rank, MPIMessage *msg);


// Called from rank 0
static int getIdleProcess(void);
static void markProcessIdle(int);
static void onTermination(void);

// Called from ranks other than 0
static void slaveProcess(int rank);

#define WORK_TAG 1 // work tag for MPI_Send and MPI_Recv

static int numProcs; // number of processors in the system

// Array of length 'numProcs'.  Only used by rank 0.
// is_busy[i] is zero iff node i+1 is idle.
static int *is_busy;

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

// Called from rank 0.
// Find the rank of a slave that is not currently busy.
static int
getIdleProcess(void) {
  int i;
  while(1) {
    for(i=0;i<numProcs-1;i++) {
      if(!is_busy[i]) {
        is_busy[i] = 1;
        return i+1;
      }
    }
  }
}

// Record the fact that a rank is idle
static void
markProcessIdle(int rank) {
  is_busy[rank-1] = 0;
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
    triolet_run_task(command.length, command.data, &slaveProcess_sendResult);
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
  MPI_Init(argc, argv);
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

// create a task from a message and the node_id
void create_task(MPITask task, int node_id) {
  //	printf("create_task: Creating task\n");
  task->rank = node_id;
}

// create a message from data and task
void create_message(MPIMessage * msg, char *data, int count) {
  msg->data = data;
  msg->length = count;
}

// This function can only be called from rank 0.
// Launch some work on an idle process.  Error if there are no idle processes.
MPITask triolet_MPITask_launch(int length, char *data) {
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

// Called from Triolet code
int32_t triolet_get_num_distributed_places(void)
{
  return numProcs;
}

#endif  /* USE_MPI */
