
#ifndef _MPI_H
#define _MPI_H

#ifdef USE_MPI

// FIXME: This should be part of a thread-state object, but the infrastructure
// for managing thread state objects isn't there
typedef struct {
  int runningDistributedTask;   /* Nonzero if running a distributed task */
} ThreadState;

typedef struct {
  int rank; //the id of node on which this task will run
} *MPITask;

typedef struct
{
  int length;
  char *data;
} MPIMessage;

// Results about an object that has been serialized,
// from 'serializeBoxedObject'
struct SerializedObjectInfo {
  uint32_t length;
  void *buffer;
};

// Launch the MPI task interface.
// If MPI rank is zero, then return.
// If MPI rank is not zero, then run a loop that waits for MPI messages.
int triolet_MPITask_setup(int *argc, char ***argv);

// This function can only be called from rank 0.
// Launch some work on an idle process.  Error if there are no idle processes.
MPITask triolet_MPITask_launch(int32_t length, char *data);

// This function can only be called from rank 0.
// Wait for some work to finish.
void *triolet_MPITask_wait(MPITask);

// This function is implemented in Triolet.  Deserialize a single object.
void *triolet_deserialize(int32_t length, char *data);

// Serialize an object to a byte array
SerializedObjectInfo triolet_serialize (void *);

// Begin executing a distributed task.
// When the main rank runs a task, it calls this function.
// Worker ranks processing 'MPITask's call this automatically.
void triolet_begin_distributed_task(void);

// Finish executing a distributed task.
// When the main rank runs a task, it calls this function.
// Worker ranks processing 'MPITask's call this automatically.
void triolet_end_distributed_task(void);

// This function is implemented in Triolet.  Run a task on a client.
int32_t triolet_run_task(int32_t length, char *data, void (*)(int32_t, char *));

// Get the number of distributed execution places
int32_t triolet_get_num_distributed_places(void);

// Check whether the current processor is executing a distributed task
int32_t triolet_in_distributed_task(void);

#endif  /* USE_MPI */

#endif
