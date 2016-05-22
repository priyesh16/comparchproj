// Paper #8
// Title: Prefetching on time and when it works
// Authors:
// Ibrahim Burak Karsli - bkarsli@ele.uri.edu - Department of Electrical, Computer and Biomedical Engineering - University of Rhode Island
// Mustafa Cavus - mcavus@my.uri.edu - Department of Electrical, Computer and Biomedical Engineering - University of Rhode Island
// Resit Sendag - sendag@ele.uri.edu - Department of Electrical, Computer and Biomedical Engineering - University of Rhode Island


#include <stdio.h>
#include <stdlib.h>
#include "../inc/prefetcher.h"


// *********************************************************************************************
// ************************************* BEGINNING OF SEQ **************************************
//**********************************************************************************************

#define MAXDISTANCE 6 // max distance pointer
#define INTERVAL 512
#define TQSIZE 128
#define PFQSIZE 128
#define IP_MASK_8b (0x0ff)
#define IP_MASK_16b (0x0ffff)
#define IP_MASK_32b (0x0ffffffff)

//prefetch usefulness
/* every 2048 accesses, 4 evaluation periods, if prefetching is on, turn-off prefetches on blocks with addr, addr%4 == 2. then at the end of the current period, check the L2 demand access miss rate on blocks that prefetching was turned off, and miss rate for all other blocks. If hit rate for other blocks is lower, turn off prefetching for the next region.*/

void l2_prefetcher_operate_mi(int cpu_num, unsigned long long int addr, unsigned long long int ip, int cache_hit);
#define TESTPERIOD 4*INTERVAL
// testing related
int testblks = 0;
int testblks_hits = 0;
int otherblks = 0;
int otherblks_hits = 0;
int testing = 0;
int testperiod = TESTPERIOD;
int nexttest = TESTPERIOD;
int cntoff = 0;
int cnton = 0;
int DIFFLIMIT = INTERVAL*0.6;
//test queue for testing timeliness and relative success
typedef struct q{
	int tail;
		struct{
		unsigned long long int addr;
	}ent[TQSIZE];
}q_t;

//prefetch queue for prefetch filtering
typedef struct pq{
	int tail;
	struct{
		unsigned long long int addr;
	}ent[PFQSIZE];
}pq_t;

pq_t *pfq;
q_t *tq;

int tqhits = 0;
int avgtqhits = 0;
int tqmhits = 0;
unsigned long long int sumdiff = 0;
int l2acc = 0;
int l2miss = 0;
int high = 0;
int low = 0;
int pfcut = 0;
int pfcut2 = 0;
int low2 = 0;
int l2_mshr_limit = 8;
int distance = 1;
int pf_turn_on = 0;
int pf_turn_off = 0;


int dist[] = {-1,-2,0,1,2,3,4,5,6,7,8,9,10,11,12};
int dist_ptr = 1; // start with offset 1


void tq_ini(){
	int i;
	for (i=0;i<TQSIZE;i++) {
		tq->ent[i].addr = 0;
	}
	tq->tail = -1;
}

int intq(unsigned long long int addr) {
	int i;
	int found = 0;
	for (i=0;i<TQSIZE;i++) {
		if (addr == tq->ent[i].addr) {
			found = 1;
			break;
		}
	}
	return found;
}

void pfq_ini() {
	int i;
	for (i=0;i<PFQSIZE;i++) {
		pfq->ent[i].addr = 0;
	}
	pfq->tail = -1;
}

int inpfq(unsigned long long int addr) {
	int i;
	int found = 0;
	for (i=0; i<PFQSIZE; i++) {
		if (addr == pfq->ent[i].addr) {
			found = 1;
			break;
		}
	}
	return found;
}

void SEQT_ini(int low_bw) {
	tq = (q_t *)malloc(sizeof(q_t));
	pfq = (pq_t *)malloc(sizeof(pq_t));
	if (low_bw) 
		DIFFLIMIT = INTERVAL * 0.5;
	tq_ini();
	pfq_ini();
}

void SEQT(unsigned long long int addr, unsigned long long int ip, int cache_hit) {
	static int suml2occ = 0;
	static int numl2occhigh = 0;
	unsigned long long int cycle = get_current_cycle(0); 
	int m;
	double tblks_hitrate; 
	double oblks_hitrate;
	int pf_off = 0;
	int failedtest;	
	int Istblk = 0;
	unsigned long long int pf_address;
	int samepage; 
	int nopf;


	suml2occ +=  get_l2_mshr_occupancy(0);
  
	if (get_l2_mshr_occupancy(0)>=15)
		numl2occhigh++;
  
	l2acc++;
	if (!cache_hit)
		l2miss++;
  
	//search for l2acc in tq
	for (m=0; m<TQSIZE; m++) {
		if (((addr&~0x3f) >> 6) == tq->ent[m].addr) {
			tqhits++;
		if (!cache_hit)
			tqmhits++;
		break;
		}
	}
  
	if ((l2acc%INTERVAL)==0) {
		//decide on distance
		if (tqhits < 16) {
			if (pfcut > 1) {
				dist_ptr = 0;
				pfcut2 = 0;
			}
			else {
				if (dist_ptr > -1)
					dist_ptr--;
			}

			if ((l2miss-tqmhits)>DIFFLIMIT)
				pfcut2++;
			else
				pfcut2 = 0;

			high = 0;
			low = 0;
			low2 = 0;
			pfcut++;
		}
		else {
			pfcut = 0;

			if (l2miss < 10) {
				pfcut2 = 0;
			}
			else if ((l2miss-tqmhits)>DIFFLIMIT) {
				low2 = 0;
				if (pfcut2 > 1){
					dist_ptr = 0;
					pfcut2 = 0;
				}
				else {
					pfcut2++;
					if (dist_ptr == 0){
						if (pf_turn_on > 1) {
							pf_turn_on = 0;
							dist_ptr = 1;
						}
						else
							pf_turn_on++;
					}
				}
				high = 0;
				low = 0;
			}
			else if ((l2miss!=0) && (tqmhits !=0)) {
				if ((l2miss/tqmhits < 2)){
					if (low2>=2) {
						if (dist_ptr < MAXDISTANCE) {
							dist_ptr++;
							low2 = 0;
						}
					}
					else
						low2++;
				}
				else
					low2 = 0;
				high = 0;
				low = 0;
				pfcut2 = 0;
		
				if (dist_ptr == 0) {
					if (pf_turn_on > 1) {
						pf_turn_on = 0;
						dist_ptr = 1;
					}
					else
						pf_turn_on++;
				}
			}
			else {
				pfcut2 = 0;
				high = 0;
				low = 0;
				low2 = 0;
			}
		}
		distance = dist[dist_ptr];

		//reset table
		tq_ini();

		avgtqhits = 0;
		tqmhits = 0;
		sumdiff = 0;
		tqhits = 0;
		l2miss = 0;
		suml2occ = 0;
		numl2occhigh = 0;
		
		//testing related
		if (testing == 1) {
			tblks_hitrate = (double)testblks_hits/(double)testblks;
			oblks_hitrate = (double)otherblks_hits/(double)otherblks;

			if (knob_low_bandwidth) {
				//turn off prefetching if really not worth it
				pf_off = ((double)oblks_hitrate < (1.2*(double)tblks_hitrate));
				if (pf_off == 0)
					pf_off = (otherblks_hits < 16);
			}
			else {
				// give advantage to prefetching
				pf_off = (((double)tblks_hitrate/(double)oblks_hitrate) > 1.2);
				if (pf_off == 0)
					pf_off = (otherblks_hits < 8);
			}
			failedtest = ((testblks < 32) || (otherblks < 32));	
			if (!failedtest) {
				if (pf_off) {
					distance = 0;
					if (testperiod > INTERVAL)
						testperiod = testperiod>>1;
					//update turning off counter
					if (cntoff < 3)
						cntoff++;
					cnton = 0;
				}
				else {
					if (testperiod < (32*INTERVAL))
						testperiod = testperiod*2;
						//update turning off counter
						cntoff = 0;
					if (cnton < 3)
						cnton++;
				}
			}
			else {
				//failed test, try again next interval
				testperiod = INTERVAL;
			}
			nexttest += testperiod;
		}
		
		testing = 0;
		testblks_hits = 0;
		testblks = 0;
		otherblks_hits = 0;
		otherblks = 0;
	}

	//for now, do this only for low bandwidth
	if (l2acc == nexttest && knob_low_bandwidth) {
		if (distance!=0)
			testing = 1;
		else
			nexttest += INTERVAL;
	}

	if (testing == 1) {
		//if keeps turning off prefetcher, increase the number of tblks
		/**/
		if (cntoff>=2)
			Istblk = (addr>>6)%3 != 1;
		else
			Istblk = (addr>>6)%4 == 2;
		if (Istblk) {
			testblks++;
			if (cache_hit)
				testblks_hits++;
		}
		else {
			otherblks++;
			if (cache_hit)
				otherblks_hits++;
		}
	}
	pf_address = ((addr>>6)+distance)<<6;
	samepage = (pf_address>>12) == (addr>>12);  
	//if distance is 0 (nopref), put in the queue as if distance = 1
	if (distance == 0)
		pf_address = ((addr>>6)+1)<<6;
	if (testing == 1) {
		//if keeps turning off prefetcher, increase the number of tblks
		/**/
		if (cntoff>=2)
			Istblk = (pf_address>>6)%3 != 1;
		else
			Istblk = (pf_address>>6)%4 == 2;
	}

	nopf = ((testing ==1) && (Istblk));
	if (!nopf) {
		if (samepage && !inpfq(pf_address >> 6)) {
			if (distance != 0){
				//todo: make occupancy limit check dynamic
				if (get_l2_mshr_occupancy(0) < l2_mshr_limit) 
					l2_prefetch_line(0, addr, pf_address, FILL_L2);
				else
					l2_prefetch_line(0, addr, pf_address, FILL_LLC);		  
				//add prefetched addr to the prefetch queue
				pfq->tail = (pfq->tail+1) % PFQSIZE;
				pfq->ent[pfq->tail].addr = (pf_address >> 6);

			}
		}
	}
	//add potential prefetch addr to the test queue
	if (samepage && !intq(pf_address>> 6)) {
		tq->tail = (tq->tail+1) % TQSIZE;
		tq->ent[tq->tail].addr = (pf_address >> 6);
	}
} // end SEQT()


// *********************************************************************************************
// ************************************* ENDING OF SEQ **************************************
//**********************************************************************************************


// *********************************************************************************************
// ******************************* BEGINNING OF IP STRIDE **************************************
//**********************************************************************************************

#define IP_TRACKER_COUNT 1024
#define IP_PREFETCH_DEGREE 1
#define IP_DISTANCE 2

typedef struct ip_tracker
{
	unsigned int ip;//32 bits  the IP we're tracking
	unsigned short last_addr;//16 bits, the last address accessed by this IP
	short last_stride;//8 bits, the stride between the last two addresses accessed by this IP
	unsigned long long int lru_cycle; // use LRU to evict old IP trackers
} ip_tracker_t;

ip_tracker_t trackers[IP_TRACKER_COUNT];

void IP_STRIDE_ini() {
	int i;
	for (i=0; i<IP_TRACKER_COUNT; i++) {
		trackers[i].ip = 0;
		trackers[i].last_addr = 0;
		trackers[i].last_stride = 0;
		trackers[i].lru_cycle = 0;
	}
}

void IP_STRIDE(unsigned long long int addr, unsigned long long int ip, int cache_hit) {
	// check for a tracker hit
	int tracker_index = -1;
	unsigned long long int addr_blk = addr >> 6;
	int i;
	int lru_index = 0;
	unsigned long long int lru_cycle;
	short stride = 0;
	int tempdist;
	unsigned long long int pf_address;

	for (i=0; i<IP_TRACKER_COUNT; i++) {
		if (trackers[i].ip == (ip & IP_MASK_32b)) {
			trackers[i].lru_cycle = get_current_cycle(0);
			tracker_index = i;
			break;
		}
	}

	if (tracker_index == -1) {
		// this is a new IP that doesn't have a tracker yet, so allocate one
		lru_cycle = trackers[lru_index].lru_cycle;
		for (i=0; i<IP_TRACKER_COUNT; i++) {
			if (trackers[i].lru_cycle < lru_cycle) {
				lru_index = i;
				lru_cycle = trackers[lru_index].lru_cycle;
			}
		}
		tracker_index = lru_index;

		// reset the old tracker
		trackers[tracker_index].ip = ip & IP_MASK_32b;
		trackers[tracker_index].last_addr = addr_blk & IP_MASK_16b;
		trackers[tracker_index].last_stride = 0;
		trackers[tracker_index].lru_cycle = get_current_cycle(0);

		return;
	}

	// calculate the stride between the current address and the last address
	// this bit appears overly complicated because we're calculating
	// differences between unsigned address variables
	if ((addr_blk & IP_MASK_16b) > trackers[tracker_index].last_addr)
		stride = ((addr_blk & IP_MASK_16b) - trackers[tracker_index].last_addr) & IP_MASK_8b;
	else {
		stride = (trackers[tracker_index].last_addr - (addr_blk & IP_MASK_16b)) & IP_MASK_8b;
		stride *= -1;
	}

	// don't do anything if we somehow saw the same address twice in a row
	if (stride == 0) 
		return;

	// only do any prefetching if there's a pattern of seeing the same
	// stride more than once
	if (stride == trackers[tracker_index].last_stride) {
		// do some prefetching
		tempdist = distance;
		tempdist = tempdist / 2;
		if (tempdist == 0) 
			tempdist = 1;
		for (i=tempdist; i<IP_PREFETCH_DEGREE+tempdist; i++) {
			//for (i=IP_DISTANCE; i<IP_PREFETCH_DEGREE+IP_DISTANCE; i++)
			pf_address = (addr_blk + (stride*(i+1))) << 6;
			// only issue a prefetch if the prefetch address is in the same 4 KB page 
			// as the current demand access address
			if ((pf_address>>12) != (addr>>12))
				break;
			// check the MSHR occupancy to decide if we're going to prefetch to the L2 or LLC
			if (!inpfq((pf_address >> 6))) {
				if (get_l2_mshr_occupancy(0) < l2_mshr_limit)
					l2_prefetch_line(0, addr, pf_address, FILL_L2);
				else
					l2_prefetch_line(0, addr, pf_address, FILL_LLC);
				pfq->tail = (pfq->tail+1) % PFQSIZE;
				pfq->ent[pfq->tail].addr = (pf_address >> 6);
			}
		}
	}

	trackers[tracker_index].last_addr = addr_blk & IP_MASK_16b;
	trackers[tracker_index].last_stride = stride;
}

		// *********************************************************************************************
		// ************************************* END OF IP STRIDE **************************************
	//**********************************************************************************************


void l2_prefetcher_initialize(int cpu_num) {
	IP_STRIDE_ini();
	SEQT_ini(knob_low_bandwidth);
}


void l2_prefetcher_operate(int cpu_num, unsigned long long int addr, unsigned long long int ip, int cache_hit) {
	IP_STRIDE(addr, ip, cache_hit);
	SEQT(addr, ip, cache_hit);  
	l2_prefetcher_operate_mi(cpu_num, addr, ip, cache_hit);
}

/*
void l2_cache_fill(int cpu_num, unsigned long long int addr, int set, int way, int prefetch, unsigned long long int evicted_addr)
{ }

void l2_prefetcher_heartbeat_stats(int cpu_num)
{ }

void l2_prefetcher_warmup_stats(int cpu_num)
{ }

void l2_prefetcher_final_stats(int cpu_num)
{ }
*/

/* --------------------------------------------Michaud code -----------------------------------*/

// Submission ID: 3

// Paper title: A Best-Offset Prefetcher

// Author: Pierre Michaud


//######################################################################################
//                             PREFETCHER PARAMETERS 
//######################################################################################

// Because prefetch cannot cross 4KB-page boundaries, there is no need to consider offsets
// greater than 63. However, with pages larger than 4KB, it would be beneficial to consider
// larger offsets.

#define NOFFSETS 46
int OFFSET[NOFFSETS] = {1,-1,2,-2,3,-3,4,-4,5,-5,6,-6,7,-7,8,-8,9,-9,10,-10,11,-11,12,-12,13,-13,14,-14,15,-15,16,-16,18,-18,20,-20,24,-24,30,-30,32,-32,36,-36,40,-40};
#define DEFAULT_OFFSET 1
#define SCORE_MAX 31
#define ROUND_MAX 100
#define RRINDEX 6
#define RRTAG 12
#define DELAYQSIZE 15
#define DELAY 60
#define TIME_BITS 12
#define LLC_RATE_MAX 255
#define GAUGE_MAX 8191
#define MSHR_THRESHOLD_MAX (L2_MSHR_COUNT-4)
#define MSHR_THRESHOLD_MIN 2
#define LOW_SCORE 20
#define BAD_SCORE ((knob_small_llc)? 10 : 1)
#define BANDWIDTH ((knob_low_bandwidth)? 64 : 16)


//######################################################################################
//                               PREFETCHER STATE
//######################################################################################

int prefetch_offset;   // 7 bits (6-bit value + 1 sign bit)

// Recent Requests (RR) table: 2 banks, 64 entries per bank, RRTAG bits per entry
int recent_request[2][1<<RRINDEX]; // 2x64x12 = 1536 bits

// 1 prefetch bit per L2 cache line : 256x8 = 2048 bits 
int prefetch_bit[L2_SET_COUNT][L2_ASSOCIATIVITY]; 


struct offsets_scores {
	int score[NOFFSETS];    // log2 SCORE_MAX = 5 bits per entry
	int max_score;          // log2 SCORE_MAX = 5 bits
	int best_offset;        // 7 bits (6-bit value + 1 sign bit)
	int round;              // log2 ROUND_MAX = 7 bits
	int p;                  // log2 NOFFSETS = 6 bits
} os;                     // 46x5+5+7+7+6 = 255 bits


struct delay_queue {
	int lineaddr[DELAYQSIZE]; // RRINDEX+RTAG = 18 bits
	int cycle[DELAYQSIZE];    // TIME_BITS = 12 bits
	int valid[DELAYQSIZE];    // 1 bit 
	int tail;                 // log2 DELAYQSIZE = 4 bits
	int head;                 // log2 DELAYQSIZE = 4 bits
} dq;                       // 15x(18+12+1)+4+4 = 473 bits


struct prefetch_throttle {
	int mshr_threshold;     // log2 L2_MSHR_COUNT = 4 bits
	int prefetch_score;     // log2 SCORE_MAX = 5 bits
	int llc_rate;           // log2 LLC_RATE_MAX = 8 bits
	int llc_rate_gauge;     // log2 GAUGE_MAX = 13 bits
	int last_cycle;         // TIME_BITS = 12 bits
} pt;                     // 4+5+8+13+12 = 42 bits

// Total prefetcher state: 7 + 1536 + 2048 + 255 + 473 + 42 = 4361 bits 


//######################################################################################
//                            SOME MACROS & DEFINITIONS
//######################################################################################

#define LOGLINE 6

#define SAMEPAGE(lineaddr1,lineaddr2) ((((lineaddr1) ^ (lineaddr2)) >> 6) == 0)

#define INCREMENT(x,n) {x++; if (x==(n)) x=0;}

#define TRUNCATE(x,nbits) (((x) & ((1<<(nbits))-1)))

typedef long long t_addr;


//######################################################################################
//                            RECENT REQUESTS TABLE (RR)
//######################################################################################

void rr_init() {
	int i;
	for (i=0; i<(1<<RRINDEX); i++) {
		recent_request[0][i] = 0;
		recent_request[1][i] = 0;
	}
}


int rr_tag(t_addr lineaddr) {
	return TRUNCATE(lineaddr>>RRINDEX,RRTAG);
}


int rr_index_left(t_addr lineaddr) {
	return TRUNCATE(lineaddr^(lineaddr>>RRINDEX),RRINDEX);
}


int rr_index_right(t_addr lineaddr) {
  return TRUNCATE(lineaddr^(lineaddr>>(2*RRINDEX)),RRINDEX);
}


void rr_insert_left(t_addr lineaddr) {
  int i = rr_index_left(lineaddr);
  recent_request[0][i] = rr_tag(lineaddr);
}


void rr_insert_right(t_addr lineaddr) {
  int i = rr_index_right(lineaddr);
  recent_request[1][i] = rr_tag(lineaddr);
}


int rr_hit(t_addr lineaddr) {
  int i = rr_index_left(lineaddr);
  int j = rr_index_right(lineaddr);
  int tag = rr_tag(lineaddr);
  return (recent_request[0][i] == tag) || (recent_request[1][j] == tag);
}



//######################################################################################
//                               DELAY QUEUE (DQ)
//######################################################################################

// Without the delay queue, the prefetcher would always try to select an offset value
// large enough for having timely prefetches. However, sometimes, a small offset yields
// late prefetches but greater prefetch accuracy and better performance. The delay queue
// is an imperfect solution to this problem.

// This implementation of the delay queue is specific to the DPC2 simulator, as the DPC2
// prefetcher can act only at certain clock cycles. In a real processor, the delay queue
// implementation can be simpler.


void dq_init() {
	int i;
	for (i=0; i<DELAYQSIZE; i++) {
		dq.lineaddr[i] = 0;
		dq.cycle[i] = 0;
		dq.valid[i] = 0;
	}
	dq.tail = 0;
	dq.head = 0;
}


void dq_push(t_addr lineaddr) {
	// enqueue one line address
	if (dq.valid[dq.tail]) {
		// delay queue is full
		// dequeue the oldest entry and write the "left" bank of the RR table
		rr_insert_left(dq.lineaddr[dq.head]);
		INCREMENT(dq.head,DELAYQSIZE);
	}
	dq.lineaddr[dq.tail] = TRUNCATE(lineaddr,RRINDEX+RRTAG);
	dq.cycle[dq.tail] = TRUNCATE(get_current_cycle(0),TIME_BITS);
	dq.valid[dq.tail] = 1;
	INCREMENT(dq.tail,DELAYQSIZE);
}

// tells whether or not the oldest entry is ready to be dequeued
int dq_ready() {
	// delay queue is empty
	if (! dq.valid[dq.head]) 
		return 0;

	int cycle = TRUNCATE(get_current_cycle(0),TIME_BITS);
	int issuecycle = dq.cycle[dq.head];
	int readycycle = TRUNCATE(issuecycle+DELAY,TIME_BITS);
	if (readycycle >= issuecycle) 
		return (cycle < issuecycle) || (cycle >= readycycle);
	else
		return (cycle < issuecycle) && (cycle >= readycycle);
}


// dequeue the entries that are ready to be dequeued,
// and do a write in the "left" bank of the RR table for each of them
void dq_pop()
{
	int i;
	for (i=0; i<DELAYQSIZE; i++) {
		if (! dq_ready()) 
			break;
		rr_insert_left(dq.lineaddr[dq.head]);
		dq.valid[dq.head] = 0;
		INCREMENT(dq.head,DELAYQSIZE);
	}
}

//######################################################################################
//                               PREFETCH THROTTLE (PT)
//######################################################################################

// The following prefetch throttling method is specific to the DPC2 simulator, as other
// parts of the microarchitecture (requests schedulers, cache replacement policy,
// LLC hit/miss information,...) can be neither modified nor observed. Consequently,
// we ignore hardware implementation considerations here.


void pt_init()
{
	pt.mshr_threshold = MSHR_THRESHOLD_MAX;
	pt.prefetch_score = SCORE_MAX;
	pt.llc_rate = 0;
	pt.llc_rate_gauge = GAUGE_MAX/2;
	pt.last_cycle = 0;
}


// The pt_update_mshr_threshold function is for adjusting the MSHR threshold
// (a prefetch request is dropped when the MSHR occupancy exceeds the threshold)

void pt_update_mshr_threshold()
{
	// prefetch accuracy not too bad, or low bandwidth requirement
	// ==> maximum prefetch aggressiveness
	if ((pt.prefetch_score > LOW_SCORE) || (pt.llc_rate > (2*BANDWIDTH))) {
		pt.mshr_threshold = MSHR_THRESHOLD_MAX;
	} else if (pt.llc_rate < BANDWIDTH) {
		// LLC access rate exceeds memory bandwidth, implying that there are some LLC hits.
		// If there are more LLC misses than hits, perhaps memory bandwidth saturates.
		// If there are more LLC hits than misses, the MSHR is probably not stressed.
		// So we set the MSHR threshold low.
		pt.mshr_threshold = MSHR_THRESHOLD_MIN;
	} else {
	// in-between situation: we set the MSHR threshold proportionally to the (inverse) LLC rate
		pt.mshr_threshold = MSHR_THRESHOLD_MIN + (MSHR_THRESHOLD_MAX-MSHR_THRESHOLD_MIN) * (double) (pt.llc_rate - BANDWIDTH) / BANDWIDTH;
	}
}


// The pt_llc_access function estimates the average time between consecutive LLC accesses.
// It is called on every LLC access.

void pt_llc_access() {
	// update the gauge
	int cycle = TRUNCATE(get_current_cycle(0),TIME_BITS);
	int dt = TRUNCATE(cycle - pt.last_cycle,TIME_BITS);
	pt.last_cycle = cycle;
	pt.llc_rate_gauge += dt - pt.llc_rate;

	// if the gauge reaches its upper limit, increment the rate counter
	// if the gauge reaches its lower limit, decrement the rate counter
	// otherwise leave the rate counter unchanged
	if (pt.llc_rate_gauge > GAUGE_MAX) {
		pt.llc_rate_gauge = GAUGE_MAX;
		if (pt.llc_rate < LLC_RATE_MAX) {
			pt.llc_rate++;
			pt_update_mshr_threshold();
		}
	} else if (pt.llc_rate_gauge < 0) {
		pt.llc_rate_gauge = 0;
		if (pt.llc_rate > 0) {
			pt.llc_rate--;
			pt_update_mshr_threshold();
		}
	}
}


//######################################################################################
//                               OFFSETS SCORES (OS)
//######################################################################################

// A method for determining the best offset value

void os_reset()
{
  int i;
  for (i=0; i<NOFFSETS; i++) {
    os.score[i] = 0;
  }
  os.max_score = 0;
  os.best_offset = 0;
  os.round = 0;
  os.p = 0;
}


// The os_learn_best_offset function tests one offset at a time, trying to determine
// if the current line would have been successfully prefetched with that offset

void os_learn_best_offset(t_addr lineaddr)
{
  int testoffset = OFFSET[os.p];
  t_addr testlineaddr = lineaddr - testoffset;

  if (SAMEPAGE(lineaddr,testlineaddr) && rr_hit(testlineaddr)) {
    // the current line would likely have been prefetched successfully with that offset
    // ==> increment the score 
    os.score[os.p]++;
    if (os.score[os.p] >= os.max_score) {
      os.max_score = os.score[os.p];
      os.best_offset = testoffset;
    }
  }

  if (os.p == (NOFFSETS-1)) {
    // one round finished
    os.round++;

    if ((os.max_score == SCORE_MAX) || (os.round == ROUND_MAX)) {
      // learning phase is finished, update the prefetch offset
      prefetch_offset = (os.best_offset != 0)? os.best_offset : DEFAULT_OFFSET;
      pt.prefetch_score = os.max_score;
      pt_update_mshr_threshold();

      if (os.max_score <= BAD_SCORE) {
	// prefetch accuracy is likely to be very low ==> turn the prefetch off 
	prefetch_offset = 0;
      }
      // new learning phase starts
      os_reset();
      return;
    }
  }
  INCREMENT(os.p,NOFFSETS); // prepare to test the next offset
}


//######################################################################################
//                               OFFSET PREFETCHER
//######################################################################################

// Issue at most one prefetch request. The prefetch line address is obtained by adding
// the prefetch offset to the current line address

int issue_prefetch(t_addr lineaddr, int offset)
{
  if (offset == 0) {
    // The prefetcher is currently turned off.
    // Just push the line address into the delay queue for best-offset learning.
    dq_push(lineaddr);
    return 0; 
  }
  if (! SAMEPAGE(lineaddr,lineaddr+offset)) {
    // crossing the page boundary, no prefetch request issued
    return 0;
  }
  if (get_l2_mshr_occupancy(0) < pt.mshr_threshold) {
    // prefetch into L2
    dq_push(lineaddr);
    return l2_prefetch_line(0,lineaddr<<LOGLINE,(lineaddr+offset)<<LOGLINE,FILL_L2);
  }
  // could not prefetch into L2
  // try to prefetch into LLC if prefetch accuracy not too bad
  if (pt.prefetch_score > LOW_SCORE) {
    return l2_prefetch_line(0,lineaddr<<LOGLINE,(lineaddr+offset)<<LOGLINE,FILL_LLC);
  }
  return 0;
}


//######################################################################################
//                               DPC2 INTERFACE
//######################################################################################


void l2_prefetcher_initialize_mi(int cpu_num)
{
  prefetch_offset = DEFAULT_OFFSET;
  rr_init();
  os_reset();
  dq_init();
  pt_init();
  int i,j;
  for (i=0; i<L2_SET_COUNT; i++) {
    for (j=0; j<L2_ASSOCIATIVITY; j++) {
      prefetch_bit[i][j] = 0;
    }
  }
}


void l2_prefetcher_operate_mi(int cpu_num, unsigned long long int addr, unsigned long long int ip, int cache_hit)
{
  t_addr lineaddr = addr >> LOGLINE;

  int s = l2_get_set(addr);
  int w = l2_get_way(0,addr,s);
  int l2_hit = (w>=0);
  int prefetched = 0;

  if (l2_hit) {
    // read the prefetch bit, and reset it
    prefetched = prefetch_bit[s][w];
    prefetch_bit[s][w] = 0;
  } else {
    pt_llc_access();
  }
 
  dq_pop();

  int prefetch_issued = 0;

  if (! l2_hit || prefetched) {
    os_learn_best_offset(lineaddr);
    prefetch_issued = issue_prefetch(lineaddr,prefetch_offset);
    if (prefetch_issued) {
      // assume the prefetch request is a L2 miss (we don't know actually)
      pt_llc_access();
    }
  }
}


void l2_cache_fill(int cpu_num, unsigned long long int addr, int set, int way, int prefetch, unsigned long long int evicted_addr)
{
  // In this version of the DPC2 simulator, the "prefetch" boolean passed
  // as input here is not reset whenever a demand request hits in the L2
  // MSHR on an in-flight prefetch request. Fortunately, this is the information
  // we need for updating the RR table for best-offset learning.
  // However, the prefetch bit stored in the L2 is not completely accurate
  // (though hopefully this does not impact performance too much).
  // In a real hardware implementation of the BO prefetcher, we would distinguish
  // "prefetched" and "demand-requested", which are independent informations.
  
  t_addr lineaddr = addr >> LOGLINE;

  // write the prefetch bit 
  int s = l2_get_set(addr);
  int w = l2_get_way(0,addr,s);
  prefetch_bit[s][w] = prefetch;

  // write the "right" bank of the RR table
  t_addr baselineaddr;
  if (prefetch || (prefetch_offset == 0)) {
    baselineaddr = lineaddr - prefetch_offset;
    if (SAMEPAGE(lineaddr,baselineaddr)) {
      rr_insert_right(baselineaddr);
    }
  }
}


void l2_prefetcher_heartbeat_stats(int cpu_num)
{
 
}

void l2_prefetcher_warmup_stats(int cpu_num)
{
  
}

void l2_prefetcher_final_stats(int cpu_num)
{
 
}
