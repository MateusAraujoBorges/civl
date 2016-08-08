/* 
 * Determines how many blocks to send to each proc in the
 * current phase.
 *
 * Preconditions:
 *    outgoing, incoming, totalOutgoing, and totalIncoming are all correct
 *    blocks are sorted.
 *
 * Postconditions:
 *   recvCount[] is updated with the number of direct blocks to
 *     receive from each proc in this phase, based on some heuristic;
 *   sendCount[] is updated to contain the number of direct blocks to
 *     send to each proc in this phase;
 *   totalSendCount = sum of sendCounts[];
 *   totalRecvCount = sum of recvCounts[];
 *
 * Current heuristic: greedy */
static void computeDirectMoves(MADRE_Object madre) {
  PH bred = (PH)madre->bred;
  int *sortVector = MADRE_BMAN_getSortVector(bred->bman);
  int totalRemaining = bred->numDead; /* remaining free space */
  int i;
  int requestCount = 0;

  if (totalRemaining == 0 && bred->totalIncoming > 0 && bred->holdIndex < 0) {
    /* use the holdBlock to avoid deadlock...*/
    totalRemaining = 1;
  }

  /* post receives for quantities from my targets */
  for (i = 0; i < madre->numProcs; i++) {
    if (bred->outgoing[i] > 0) {
      MPI_Irecv(bred->sendCounts + i, 1, MPI_INT, i, bred->tag, madre->comm,
		bred->requests + requestCount);
      requestCount++;
    }
  }
  /* post send quantities to my sources */
  bred->totalRecvCount = 0;
  for (i = 0; i < madre->numProcs; i++) {
    int requested = bred->incoming[i];

    if (requested > 0) {
      int granted = (requested < totalRemaining ? requested : totalRemaining);

      totalRemaining -= granted;
      bred->recvCounts[i] = granted;
      MPI_Isend(bred->recvCounts + i, 1, MPI_INT, i, bred->tag, madre->comm,
		bred->requests + requestCount);
      requestCount++;
      bred->totalRecvCount += granted;
    }
  }
  /* wait for all requests to complete and update totalSendCount */
  MPI_Waitall(requestCount, bred->requests, MPI_STATUSES_IGNORE);
  bred->totalSendCount = 0;
  for (i = 0; i < madre->numProcs; i++) {
    bred->totalSendCount += bred->sendCounts[i];
  }
}
