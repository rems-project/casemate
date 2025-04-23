#ifndef CASEMATE_SYNC_H
#define CASEMATE_SYNC_H

void init_sm_lock(void);
void lock_sm(void);
void unlock_sm(void);

#define LOAD_RLX(L) \
  *((volatile typeof(L)*)&L)

#define STORE_RLX(L, V) \
  *((volatile typeof(L)*)(&L)) = V

#endif /* CASEMATE_SYNC_H */