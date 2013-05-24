
#ifndef _MPI_H
#define _MPI_H

#ifdef USE_MPI

typedef struct {
  int rank; //the id of node on which this task will run
} *MPITask;

typedef struct
{
  int length;
  char *data;
} MPIMessage;

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

// This function is implemented in Triolet.  Run a task on a client.
int32_t triolet_run_task(int32_t length, char *data, void (*)(int32_t, char *));

// Exported to Triolet
int32_t triolet_get_num_distributed_places(void);


#endif  /* USE_MPI */

#endif
