// Equihash solver
// Copyright (c) 2016 John Tromp, The Zcash developers

// Fix N, K, such that n = N/(k+1) is integer
// Fix M = 2^{n+1} hashes each of length N bits,
// H_0, ... , H_{M-1}, generated from (n+1)-bit indices.
// Problem: find binary tree on 2^K distinct indices,
// for which the exclusive-or of leaf hashes is all 0s.
// Additionally, it should satisfy the Wagner conditions:
// for each height i subtree, the exclusive-or
// of its 2^i corresponding hashes starts with i*n 0 bits,
// and for i>0 the leftmost leaf of its left subtree
// is less than the leftmost leaf of its right subtree

// The algorithm below solves this by maintaining the trees
// in a graph of K layers, each split into buckets
// with buckets indexed by the first n-RESTBITS bits following
// the i*n 0s, each bucket having 4 * 2^RESTBITS slots,
// twice the number of subtrees expected to land there.

#ifndef ZCASH_POW_TROMP_EQUI_MINER_H
#define ZCASH_POW_TROMP_EQUI_MINER_H

#include "equi.h"

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#ifdef __linux__
#include <sys/mman.h>
#endif

typedef uint16_t u16;
typedef uint64_t u64;

#ifdef EQUIHASH_TROMP_ATOMIC
#include <stdatomic.h>
typedef atomic_uint au32;
#else
typedef u32 au32;
#endif

#ifndef RESTBITS
#define RESTBITS	8
#endif

// 2_log of number of buckets
#define BUCKBITS (DIGITBITS-RESTBITS)

#ifndef SAVEMEM
#if RESTBITS == 4
// can't save memory in such small buckets
#define SAVEMEM 1
#elif RESTBITS >= 8
// take advantage of law of large numbers (sum of 2^8 random numbers)
// this reduces (200,9) memory to under 144MB, with negligible discarding
#define SAVEMEM 9/14
#endif
#endif

// number of buckets
#define NBUCKETS (1<<BUCKBITS)
// 2_log of number of slots per bucket
#define SLOTBITS (RESTBITS+1+1)
#define SLOTRANGE (1<<SLOTBITS)
#ifdef SLOTDIFF
static const u32 SLOTMSB = 1<<(SLOTBITS-1);
#endif
// number of slots per bucket
#define NSLOTS (SLOTRANGE * SAVEMEM)
// number of per-xhash slots
#define XFULL 16
// SLOTBITS mask
static const u32 SLOTMASK = SLOTRANGE-1;
// number of possible values of xhash (rest of n) bits
#define NRESTS (1<<RESTBITS)
// number of blocks of hashes extracted from single 512 bit blake2b output
#define NBLOCKS ((NHASHES+HASHESPERBLAKE-1)/HASHESPERBLAKE)
// nothing larger found in 100000 runs
static const u32 MAXSOLS = 8;

// tree node identifying its children as two different slots in
// a bucket on previous layer with the same rest bits (x-tra hash)
struct tree {
  u32 bid_s0_s1; // manual bitfields
};
typedef struct tree tree;

  tree tree_from_idx(const u32 idx) {
    tree t;
    t.bid_s0_s1 = idx;
    return t;
  }
  tree tree_from_bid(const u32 bid, const u32 s0, const u32 s1) {
    tree t;
#ifdef SLOTDIFF
    u32 ds10 = (s1 - s0) & SLOTMASK;
    if (ds10 & SLOTMSB) {
      bid_s0_s1 = (((bid << SLOTBITS) | s1) << (SLOTBITS-1)) | (SLOTMASK & ~ds10);
    } else {
      bid_s0_s1 = (((bid << SLOTBITS) | s0) << (SLOTBITS-1)) | (ds10 - 1);
    }
#else
    t.bid_s0_s1 = (((bid << SLOTBITS) | s0) << SLOTBITS) | s1;
#endif
    return t;
  }
  u32 getindex(const tree *t) {
    return t->bid_s0_s1;
  }
  u32 bucketid(const tree *t) {
#ifdef SLOTDIFF
    return t->bid_s0_s1 >> (2 * SLOTBITS - 1);
#else
    return t->bid_s0_s1 >> (2 * SLOTBITS);
#endif
  }
  u32 slotid0(const tree *t) {
#ifdef SLOTDIFF
    return (t->bid_s0_s1 >> (SLOTBITS-1)) & SLOTMASK;
#else
    return (t->bid_s0_s1 >> SLOTBITS) & SLOTMASK;
#endif
  }
  u32 slotid1(const tree *t) {
#ifdef SLOTDIFF
    return (slotid0() + 1 + (t->bid_s0_s1 & (SLOTMASK>>1))) & SLOTMASK;
#else
    return t->bid_s0_s1 & SLOTMASK;
#endif
  }

union hashunit {
  u32 word;
  uchar bytes[sizeof(u32)];
};
typedef union hashunit hashunit;

#define WORDS(bits)	((bits + 31) / 32)
#define HASHWORDS0 WORDS(WN - DIGITBITS + RESTBITS)
#define HASHWORDS1 WORDS(WN - 2*DIGITBITS + RESTBITS)

// Buckets reserve enough words for the first round on each parity. Within a
// bucket, completed tree columns are retained and current hashes are packed:
// [tree round 0][tree round 2]...[current hashes at their current width].
// Each tree column holds NSLOTS attributes; hash rows have no fixed stride.
typedef hashunit bucket0[NSLOTS * (1 + HASHWORDS0)];
typedef hashunit bucket1[NSLOTS * (1 + HASHWORDS1)];
// the N-bit hash consists of K+1 n-bit "digits"
// each of which corresponds to a layer of NBUCKETS buckets
typedef bucket0 digit0[NBUCKETS];
typedef bucket1 digit1[NBUCKETS];

// size (in bytes) of hash in round 0 <= r < WK
u32 hashsize(const u32 r) {
  const u32 hashbits = WN - (r+1) * DIGITBITS + RESTBITS;
  return (hashbits + 7) / 8;
}

u32 hashwords(u32 bytes) {
  return (bytes + 3) / 4;
}

// manages hash and tree data
struct htalloc {
  u32 *heap0;
  u32 *heap1;
  bucket0 *trees0[(WK+1)/2];
  bucket1 *trees1[WK/2];
  u32 alloced;
};
typedef struct htalloc htalloc;
  htalloc htalloc_new() {
    htalloc hta;
    hta.alloced = 0;
    return hta;
  }
  void *htalloc_alloc(htalloc *hta, const u32 n, const u32 sz);
  static void *htalloc_alloctable(htalloc *hta, const u32 sz) {
#if defined(__linux__) && defined(MADV_HUGEPAGE)
    // Anonymous mappings supply zero-filled pages without eagerly touching
    // the tables. Huge pages are an optional hint; ordinary pages also work.
    void *mem = mmap(NULL, sz, PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (mem == MAP_FAILED)
      abort();
    (void)madvise(mem, sz, MADV_HUGEPAGE);
    hta->alloced += sz;
    return mem;
#else
    return htalloc_alloc(hta, 1, sz);
#endif
  }
  static void htalloc_freetable(void *mem, const u32 sz) {
#if defined(__linux__) && defined(MADV_HUGEPAGE)
    if (mem != NULL)
      (void)munmap(mem, sz);
#else
    (void)sz;
    free(mem);
#endif
  }
  void alloctrees(htalloc *hta) {
    // Preserve earlier tree columns while reusing the shrinking hash area.
    assert(DIGITBITS >= 16); // ensures hashes shorten by 1 unit every 2 digits
    hta->alloced = 0;
    hta->heap0 = (u32 *)htalloc_alloctable(hta, sizeof(digit0));
    hta->heap1 = (u32 *)htalloc_alloctable(hta, sizeof(digit1));
    for (int r=0; r<WK; r++) {
      const u32 reserved = 1 + ((r&1) ? HASHWORDS1 : HASHWORDS0);
      assert((u32)r/2 + 1 + hashwords(hashsize(r)) <= reserved);
      if ((r&1) == 0)
        hta->trees0[r/2]  = (bucket0 *)(hta->heap0 + (r/2) * NSLOTS);
      else
        hta->trees1[r/2]  = (bucket1 *)(hta->heap1 + (r/2) * NSLOTS);
    }
  }
  void dealloctrees(htalloc *hta) {
    if (hta == NULL) {
      return;
    }

    htalloc_freetable(hta->heap0, sizeof(digit0));
    htalloc_freetable(hta->heap1, sizeof(digit1));
    // Avoid use-after-free and double-free
    hta->heap0 = NULL;
    hta->heap1 = NULL;

    for (int r=0; r<WK; r++)
      if ((r&1) == 0)
        hta->trees0[r/2]  = NULL;
      else
        hta->trees1[r/2]  = NULL;
    hta->alloced = 0;
  }
  void *htalloc_alloc(htalloc *hta, const u32 n, const u32 sz) {
    void *mem  = calloc(n, sz);
    assert(mem);
    hta->alloced += n * sz;
    return mem;
  }

typedef au32 bsizes[NBUCKETS];

u32 minu32(const u32 a, const u32 b) {
  return a < b ? a : b;
}

struct equi {
  BLAKE2bState* blake_ctx;
  blake2b_clone blake2b_clone;
  blake2b_free blake2b_free;
  blake2b_generate_hashes blake2b_generate_hashes;
  htalloc hta;
  bsizes *nslots; // PUT IN BUCKET STRUCT
  // A half-full hash set detects repeated leaves without sorting a proof.
  // Epoch tags avoid clearing the set for every rejected candidate.
  u32 index_keys[2 * PROOFSIZE];
  u32 index_tags[2 * PROOFSIZE];
  u32 index_epoch;
  proof *sols;
  au32 nsols;
  u32 xfull;
  u32 hfull;
  u32 bfull;
};
typedef struct equi equi;
  void equi_clearslots(equi *eq);
  equi *equi_new(
    blake2b_clone blake2b_clone,
    blake2b_free blake2b_free,
    blake2b_generate_hashes blake2b_generate_hashes
  ) {
    assert(sizeof(hashunit) == 4);
    equi *eq = malloc(sizeof(equi));
    eq->blake2b_clone = blake2b_clone;
    eq->blake2b_free = blake2b_free;
    eq->blake2b_generate_hashes = blake2b_generate_hashes;

    alloctrees(&eq->hta);
    eq->nslots = (bsizes *)htalloc_alloc(&eq->hta, 2 * NBUCKETS, sizeof(au32));
    eq->sols   =  (proof *)htalloc_alloc(&eq->hta, MAXSOLS, sizeof(proof));

    // C malloc() does not guarantee zero-initialized memory (but calloc() does)
    eq->blake_ctx = NULL;
    eq->nsols = 0;
    memset(eq->index_tags, 0, sizeof(eq->index_tags));
    eq->index_epoch = 0;
    equi_clearslots(eq);

    return eq;
  }
  void equi_free(equi *eq) {
    if (eq == NULL) {
      return;
    }

    dealloctrees(&eq->hta);

    free(eq->nslots);
    free(eq->sols);
    eq->blake2b_free(eq->blake_ctx);
    // Avoid use-after-free and double-free
    eq->nslots = NULL;
    eq->sols = NULL;
    eq->blake_ctx = NULL;

    free(eq);
  }
  void equi_setstate(equi *eq, const BLAKE2bState *ctx) {
    if (eq->blake_ctx) {
      eq->blake2b_free(eq->blake_ctx);
    }

    eq->blake_ctx = eq->blake2b_clone(ctx);
    memset(eq->nslots, 0, NBUCKETS * sizeof(au32)); // only nslots[0] needs zeroing
    equi_clearslots(eq);
    eq->nsols = 0;
    memset(eq->index_tags, 0, sizeof(eq->index_tags));
    eq->index_epoch = 0;
  }
  void equi_clearslots(equi *eq) {
    eq->xfull = eq->bfull = eq->hfull = 0;
  }
  u32 getslot(equi *eq, const u32 r, const u32 bucketi) {
#ifdef EQUIHASH_TROMP_ATOMIC
    return std::atomic_fetch_add_explicit(&eq->nslots[r&1][bucketi], 1U, std::memory_order_relaxed);
#else
    return eq->nslots[r&1][bucketi]++;
#endif
  }
  u32 getnslots(equi *eq, const u32 r, const u32 bid) { // SHOULD BE METHOD IN BUCKET STRUCT
    au32 *nslot = &eq->nslots[r&1][bid];
    const u32 n = minu32(*nslot, NSLOTS);
    *nslot = 0;
    return n;
  }
  void orderindices(u32 *indices, u32 size) {
    if (indices[0] > indices[size]) {
      for (u32 i=0; i < size; i++) {
        const u32 tmp = indices[i];
        indices[i] = indices[size+i];
        indices[size+i] = tmp;
      }
    }
  }
  void listindices1(equi *eq, u32 r, const tree t, u32 *indices);
  void listindices0(equi *eq, u32 r, const tree t, u32 *indices) {
    if (r == 0) {
      *indices = getindex(&t);
      return;
    }
    const tree *buck = (const tree *)&eq->hta.trees1[--r/2][bucketid(&t)];
    const u32 size = 1 << r;
    u32 *indices1 = indices + size;
    listindices1(eq, r, buck[slotid0(&t)], indices);
    listindices1(eq, r, buck[slotid1(&t)], indices1);
    orderindices(indices, size);
  }
  void listindices1(equi *eq, u32 r, const tree t, u32 *indices) {
    const tree *buck = (const tree *)&eq->hta.trees0[--r/2][bucketid(&t)];
    const u32 size = 1 << r;
    u32 *indices1 = indices + size;
    listindices0(eq, r, buck[slotid0(&t)], indices);
    listindices0(eq, r, buck[slotid1(&t)], indices1);
    orderindices(indices, size);
  }
  static bool unique_indices1(equi *eq, u32 r, tree t);
  static bool unique_indices0(equi *eq, u32 r, tree t) {
    if (r == 0) {
      const u32 key = getindex(&t);
      u32 slot = (key * 0x9e3779b1U) >> (32 - (WK + 1));
      while (eq->index_tags[slot] == eq->index_epoch) {
        if (eq->index_keys[slot] == key) return false;
        slot = (slot + 1) & (2 * PROOFSIZE - 1);
      }
      eq->index_tags[slot] = eq->index_epoch;
      eq->index_keys[slot] = key;
      return true;
    }
    const tree *buck = (const tree *)&eq->hta.trees1[--r/2][bucketid(&t)];
    return unique_indices1(eq, r, buck[slotid0(&t)]) &&
           unique_indices1(eq, r, buck[slotid1(&t)]);
  }
  static bool unique_indices1(equi *eq, u32 r, tree t) {
    const tree *buck = (const tree *)&eq->hta.trees0[--r/2][bucketid(&t)];
    return unique_indices0(eq, r, buck[slotid0(&t)]) &&
           unique_indices0(eq, r, buck[slotid1(&t)]);
  }
  void candidate(equi *eq, const tree t) {
    if (++eq->index_epoch == 0) {
      memset(eq->index_tags, 0, sizeof(eq->index_tags));
      eq->index_epoch = 1;
    }
    if (!unique_indices1(eq, WK, t)) return;
#ifdef EQUIHASH_TROMP_ATOMIC
    u32 soli = std::atomic_fetch_add_explicit(&eq->nsols, 1U, std::memory_order_relaxed);
#else
    u32 soli = eq->nsols++;
#endif
    if (soli < MAXSOLS)
      listindices1(eq, WK, t, eq->sols[soli]); // assume WK odd
  }
#ifdef EQUIHASH_SHOW_BUCKET_SIZES
  void showbsizes(equi *eq, u32 r) {
#if defined(HIST) || defined(SPARK) || defined(LOGSPARK)
    u32 binsizes[65];
    memset(binsizes, 0, 65 * sizeof(u32));
    for (u32 bucketid = 0; bucketid < NBUCKETS; bucketid++) {
      u32 bsize = minu32(eq->nslots[r&1][bucketid], NSLOTS) >> (SLOTBITS-6);
      binsizes[bsize]++;
    }
    for (u32 i=0; i < 65; i++) {
#ifdef HIST
//      printf(" %d:%d", i, binsizes[i]);
#else
#ifdef SPARK
      u32 sparks = binsizes[i] / SPARKSCALE;
#else
      u32 sparks = 0;
      for (u32 bs = binsizes[i]; bs; bs >>= 1) sparks++;
      sparks = sparks * 7 / SPARKSCALE;
#endif
//      printf("\342\226%c", '\201' + sparks);
#endif
    }
//    printf("\n");
#endif
  }
#endif

  struct htlayout {
    htalloc hta;
    u32 prevhashunits;
    u32 nexthashunits;
    u32 dunits;
    u32 prevbo;
    u32 nextbo;
  };
  typedef struct htlayout htlayout;

    htlayout htlayout_new(equi *eq, u32 r) {
      htlayout htl;
      htl.hta = eq->hta;
      htl.prevhashunits = 0;
      htl.dunits = 0;
      u32 nexthashbytes = hashsize(r);
      htl.nexthashunits = hashwords(nexthashbytes);
      htl.prevbo = 0;
      htl.nextbo = htl.nexthashunits * sizeof(hashunit) - nexthashbytes; // 0-3
      if (r) {
        u32 prevhashbytes = hashsize(r-1);
        htl.prevhashunits = hashwords(prevhashbytes);
        htl.prevbo = htl.prevhashunits * sizeof(hashunit) - prevhashbytes; // 0-3
        htl.dunits = htl.prevhashunits - htl.nexthashunits;
      }
      return htl;
    }
    u32 getxhash0(const htlayout *htl, const hashunit* hash) {
#if WN == 200 && RESTBITS == 4
      return hash->bytes[htl->prevbo] >> 4;
#elif WN == 200 && RESTBITS == 8
      return (hash->bytes[htl->prevbo] & 0xf) << 4 | hash->bytes[htl->prevbo+1] >> 4;
#elif WN == 200 && RESTBITS == 9
      return (hash->bytes[htl->prevbo] & 0x1f) << 4 | hash->bytes[htl->prevbo+1] >> 4;
#elif WN == 144 && RESTBITS == 4
      return hash->bytes[htl->prevbo] & 0xf;
#else
#error non implemented
#endif
    }
    u32 getxhash1(const htlayout *htl, const hashunit* hash) {
#if WN == 200 && RESTBITS == 4
      return hash->bytes[htl->prevbo] & 0xf;
#elif WN == 200 && RESTBITS == 8
      return hash->bytes[htl->prevbo];
#elif WN == 200 && RESTBITS == 9
      return (hash->bytes[htl->prevbo]&1) << 8 | hash->bytes[htl->prevbo+1];
#elif WN == 144 && RESTBITS == 4
      return hash->bytes[htl->prevbo] & 0xf;
#else
#error non implemented
#endif
    }
    bool htlayout_equal(const htlayout *htl, const hashunit *hash0, const hashunit *hash1) {
      return hash0[htl->prevhashunits-1].word == hash1[htl->prevhashunits-1].word;
    }

#if RESTBITS <= 6
    typedef uchar xslot;
#else
    typedef u16 xslot;
#endif
  struct collisiondata {
#ifdef XBITMAP
#if NSLOTS > 64
#error cant use XBITMAP with more than 64 slots
#endif
    u64 xhashmap[NRESTS];
    u64 xmap;
#else
    xslot nxhashslots[NRESTS];
    xslot head[NRESTS];
    xslot next[NSLOTS];
    xslot tail[NRESTS];
    u32 n0;
    u32 n1;
#endif
    u32 s0;
  };
  typedef struct collisiondata collisiondata;

    void collisiondata_clear(collisiondata *cd) {
#ifdef XBITMAP
      memset(cd->xhashmap, 0, NRESTS * sizeof(u64));
#else
      memset(cd->nxhashslots, 0, NRESTS * sizeof(xslot));
      memset(cd->head, 0, NRESTS * sizeof(xslot));
#endif
    }
    bool addslot(collisiondata *cd, u32 s1, u32 xh) {
#ifdef XBITMAP
      xmap = xhashmap[xh];
      xhashmap[xh] |= (u64)1 << s1;
      s0 = -1;
      return true;
#else
      cd->n1 = (u32)cd->nxhashslots[xh]++;
      if (cd->n1 >= XFULL)
        return false;
      if (cd->n1) {
        cd->s0 = cd->head[xh];
        cd->next[cd->tail[xh]] = s1;
      } else {
        cd->head[xh] = s1;
        cd->s0 = s1;
      }
      cd->tail[xh] = s1;
      cd->n0 = 0;
      return true;
#endif
    }
    bool nextcollision(const collisiondata *cd) {
#ifdef XBITMAP
      return cd->xmap != 0;
#else
      return cd->n0 < cd->n1;
#endif
    }
    u32 slot(collisiondata *cd) {
#ifdef XBITMAP
      const u32 ffs = __builtin_ffsll(cd->xmap);
      s0 += ffs; cd->xmap >>= ffs;
      return s0;
#else
      const u32 slot = cd->s0;
      cd->s0 = cd->next[slot];
      cd->n0++;
      return slot;
#endif
    }

  // Prefetch scattered destinations before copying the hash batch. Sources
  // remain live in the batch buffer until every pending output is flushed.
  struct pending_initial {
    tree *attr;
    hashunit *hash;
    const uchar *source;
    u32 index;
  };
  static void flush_initial(struct pending_initial *pending, u32 count,
                            u32 hashbytes, u32 nextbo) {
    for (u32 i = 0; i < count; i++) {
      *pending[i].attr = tree_from_idx(pending[i].index);
      memcpy(pending[i].hash->bytes + nextbo, pending[i].source, hashbytes);
    }
  }
  void equi_digit0(equi *eq, const u32 id) {
    // Keep hash-state clones in Rust and amortize the callback over a batch.
    enum { HASH_BATCH_SIZE = 64 };
    uchar hashes[HASH_BATCH_SIZE * HASHOUT];
    struct pending_initial pending[HASH_BATCH_SIZE];
    u32 npending = 0;
    htlayout htl = htlayout_new(eq, 0);
    const u32 hashbytes = hashsize(0);
    for (u32 block = id; block < NBLOCKS;) {
      const u32 count = minu32(HASH_BATCH_SIZE, NBLOCKS - block);
      eq->blake2b_generate_hashes(eq->blake_ctx, block, count, hashes, HASHOUT);
      for (u32 offset = 0; offset < count; offset++) {
        const uchar *hash = hashes + offset * HASHOUT;
        for (u32 i = 0; i<HASHESPERBLAKE; i++) {
          const uchar *ph = hash + i * WN/8;
#if BUCKBITS == 16 && RESTBITS == 4
          const u32 bucketid = ((u32)ph[0] << 8) | ph[1];
#elif BUCKBITS == 12 && RESTBITS == 8
          const u32 bucketid = ((u32)ph[0] << 4) | ph[1] >> 4;
#elif BUCKBITS == 11 && RESTBITS == 9
          const u32 bucketid = ((u32)ph[0] << 3) | ph[1] >> 5;
#elif BUCKBITS == 20 && RESTBITS == 4
          const u32 bucketid = ((((u32)ph[0] << 8) | ph[1]) << 4) | ph[2] >> 4;
#elif BUCKBITS == 12 && RESTBITS == 4
          const u32 bucketid = ((u32)ph[0] << 4) | ph[1] >> 4;
          const u32 xhash = ph[1] & 0xf;
#else
#error not implemented
#endif
          const u32 slot = getslot(eq, 0, bucketid);
          if (slot >= NSLOTS) {
            eq->bfull++;
            continue;
          }
          tree *attrs = (tree *)&eq->hta.trees0[0][bucketid];
          hashunit *hash = (hashunit *)(attrs + NSLOTS) + slot * htl.nexthashunits;
#if defined(__GNUC__) || defined(__clang__)
          __builtin_prefetch(attrs + slot, 1, 3);
          __builtin_prefetch(hash, 1, 3);
          __builtin_prefetch((uchar *)hash + (htl.nexthashunits - 1) * sizeof(hashunit), 1, 3);
#endif
          struct pending_initial *out = &pending[npending++];
          out->attr = attrs + slot;
          out->hash = hash;
          out->source = ph + WN/8 - hashbytes;
          out->index = (block + offset) * HASHESPERBLAKE + i;
          if (npending == HASH_BATCH_SIZE) {
            flush_initial(pending, npending, hashbytes, htl.nextbo);
            npending = 0;
          }
        }
      }
      flush_initial(pending, npending, hashbytes, htl.nextbo);
      npending = 0;
      block += count;
    }
  }

  enum { OUTPUT_BATCH_SIZE = 64 };
  // Hash inputs belong to the previous parity and stay live throughout this
  // round. Delaying the XOR lets the destination prefetch finish first.
  struct pending_output {
    tree *attr_destination;
    hashunit *hash_destination;
    tree attr;
    const hashunit *left;
    const hashunit *right;
  };
  static void flush_output(struct pending_output *pending, u32 count,
                           u32 hashunits, u32 dunits) {
    for (u32 i = 0; i < count; i++) {
      *pending[i].attr_destination = pending[i].attr;
#ifdef _MSC_VER
      hashunit *__restrict destination = pending[i].hash_destination;
#else
      hashunit *restrict destination = pending[i].hash_destination;
#endif
      for (u32 j = 0; j < hashunits; j++)
        destination[j].word = pending[i].left[j + dunits].word ^
                              pending[i].right[j + dunits].word;
    }
  }

  void equi_digitodd(equi *eq, const u32 r, const u32 id) {
    htlayout htl = htlayout_new(eq, r);
    collisiondata cd;
    struct pending_output pending[OUTPUT_BATCH_SIZE];
    u32 npending = 0;
    for (u32 bucketid=id; bucketid < NBUCKETS; bucketid++) {
      collisiondata_clear(&cd);
      hashunit *buck = (hashunit *)&htl.hta.trees0[(r-1)/2][bucketid] + NSLOTS;
      u32 bsize = getnslots(eq, r-1, bucketid);
      for (u32 s1 = 0; s1 < bsize; s1++) {
        const hashunit *pslot1 = buck + s1 * htl.prevhashunits;
        if (!addslot(&cd, s1, getxhash0(&htl, pslot1))) {
          eq->xfull++;
          continue;
        }
        for (; nextcollision(&cd); ) {
          const u32 s0 = slot(&cd);
          const hashunit *pslot0 = buck + s0 * htl.prevhashunits;
          if (htlayout_equal(&htl, pslot0, pslot1)) {
            eq->hfull++;
            continue;
          }
          u32 xorbucketid;
          const uchar *bytes0 = pslot0->bytes, *bytes1 = pslot1->bytes;
#if WN == 200 && BUCKBITS == 12 && RESTBITS == 8
          xorbucketid = (((u32)(bytes0[htl.prevbo+1] ^ bytes1[htl.prevbo+1]) & 0xf) << 8)
                             | (bytes0[htl.prevbo+2] ^ bytes1[htl.prevbo+2]);
#elif WN == 200 && BUCKBITS == 11 && RESTBITS == 9
          xorbucketid = (((u32)(bytes0[htl.prevbo+1] ^ bytes1[htl.prevbo+1]) & 0xf) << 7)
                             | (bytes0[htl.prevbo+2] ^ bytes1[htl.prevbo+2]) >> 1;
#elif WN == 144 && BUCKBITS == 20 && RESTBITS == 4
          xorbucketid = ((((u32)(bytes0[htl.prevbo+1] ^ bytes1[htl.prevbo+1]) << 8)
                              | (bytes0[htl.prevbo+2] ^ bytes1[htl.prevbo+2])) << 4)
                              | (bytes0[htl.prevbo+3] ^ bytes1[htl.prevbo+3]) >> 4;
#elif WN == 96 && BUCKBITS == 12 && RESTBITS == 4
          xorbucketid = ((u32)(bytes0[htl.prevbo+1] ^ bytes1[htl.prevbo+1]) << 4)
                            | (bytes0[htl.prevbo+2] ^ bytes1[htl.prevbo+2]) >> 4;
#else
#error not implemented
#endif
          const u32 xorslot = getslot(eq, r, xorbucketid);
          if (xorslot >= NSLOTS) {
            eq->bfull++;
            continue;
          }
          tree *attrs = (tree *)&htl.hta.trees1[r/2][xorbucketid];
          hashunit *xs = (hashunit *)(attrs + NSLOTS) + xorslot * htl.nexthashunits;
#if defined(__GNUC__) || defined(__clang__)
          __builtin_prefetch(attrs + xorslot, 1, 3);
          __builtin_prefetch(xs, 1, 3);
          __builtin_prefetch((uchar *)xs + (htl.nexthashunits - 1) * sizeof(hashunit), 1, 3);
#endif
          struct pending_output *out = &pending[npending++];
          out->attr_destination = attrs + xorslot;
          out->hash_destination = xs;
          out->attr = tree_from_bid(bucketid, s0, s1);
          out->left = pslot0;
          out->right = pslot1;
          if (npending == OUTPUT_BATCH_SIZE) {
            flush_output(pending, npending, htl.nexthashunits, htl.dunits);
            npending = 0;
          }
        }
      }
    }
    flush_output(pending, npending, htl.nexthashunits, htl.dunits);
  }

  void equi_digiteven(equi *eq, const u32 r, const u32 id) {
    htlayout htl = htlayout_new(eq, r);
    collisiondata cd;
    struct pending_output pending[OUTPUT_BATCH_SIZE];
    u32 npending = 0;
    for (u32 bucketid=id; bucketid < NBUCKETS; bucketid++) {
      collisiondata_clear(&cd);
      hashunit *buck = (hashunit *)&htl.hta.trees1[(r-1)/2][bucketid] + NSLOTS;
      u32 bsize = getnslots(eq, r-1, bucketid);
      for (u32 s1 = 0; s1 < bsize; s1++) {
        const hashunit *pslot1 = buck + s1 * htl.prevhashunits;
        if (!addslot(&cd, s1, getxhash1(&htl, pslot1))) {
          eq->xfull++;
          continue;
        }
        for (; nextcollision(&cd); ) {
          const u32 s0 = slot(&cd);
          const hashunit *pslot0 = buck + s0 * htl.prevhashunits;
          if (htlayout_equal(&htl, pslot0, pslot1)) {
            eq->hfull++;
            continue;
          }
          u32 xorbucketid;
          const uchar *bytes0 = pslot0->bytes, *bytes1 = pslot1->bytes;
#if WN == 200 && BUCKBITS == 12 && RESTBITS == 8
          xorbucketid = ((u32)(bytes0[htl.prevbo+1] ^ bytes1[htl.prevbo+1]) << 4)
                            | (bytes0[htl.prevbo+2] ^ bytes1[htl.prevbo+2]) >> 4;
#elif WN == 200 && BUCKBITS == 11 && RESTBITS == 9
          xorbucketid = ((u32)(bytes0[htl.prevbo+2] ^ bytes1[htl.prevbo+2]) << 3)
                            | (bytes0[htl.prevbo+3] ^ bytes1[htl.prevbo+3]) >> 5;
#elif WN == 144 && BUCKBITS == 20 && RESTBITS == 4
          xorbucketid = ((((u32)(bytes0[htl.prevbo+1] ^ bytes1[htl.prevbo+1]) << 8)
                              | (bytes0[htl.prevbo+2] ^ bytes1[htl.prevbo+2])) << 4)
                              | (bytes0[htl.prevbo+3] ^ bytes1[htl.prevbo+3]) >> 4;
#elif WN == 96 && BUCKBITS == 12 && RESTBITS == 4
          xorbucketid = ((u32)(bytes0[htl.prevbo+1] ^ bytes1[htl.prevbo+1]) << 4)
                            | (bytes0[htl.prevbo+2] ^ bytes1[htl.prevbo+2]) >> 4;
#else
#error not implemented
#endif
          const u32 xorslot = getslot(eq, r, xorbucketid);
          if (xorslot >= NSLOTS) {
            eq->bfull++;
            continue;
          }
          tree *attrs = (tree *)&htl.hta.trees0[r/2][xorbucketid];
          hashunit *xs = (hashunit *)(attrs + NSLOTS) + xorslot * htl.nexthashunits;
#if defined(__GNUC__) || defined(__clang__)
          __builtin_prefetch(attrs + xorslot, 1, 3);
          __builtin_prefetch(xs, 1, 3);
          __builtin_prefetch((uchar *)xs + (htl.nexthashunits - 1) * sizeof(hashunit), 1, 3);
#endif
          struct pending_output *out = &pending[npending++];
          out->attr_destination = attrs + xorslot;
          out->hash_destination = xs;
          out->attr = tree_from_bid(bucketid, s0, s1);
          out->left = pslot0;
          out->right = pslot1;
          if (npending == OUTPUT_BATCH_SIZE) {
            flush_output(pending, npending, htl.nexthashunits, htl.dunits);
            npending = 0;
          }
        }
      }
    }
    flush_output(pending, npending, htl.nexthashunits, htl.dunits);
  }

  void equi_digitK(equi *eq, const u32 id) {
    collisiondata cd;
    htlayout htl = htlayout_new(eq, WK);
    for (u32 bucketid = id; bucketid < NBUCKETS; bucketid++) {
      collisiondata_clear(&cd);
      hashunit *buck = (hashunit *)&htl.hta.trees0[(WK-1)/2][bucketid] + NSLOTS;
      u32 bsize = getnslots(eq, WK-1, bucketid);
      for (u32 s1 = 0; s1 < bsize; s1++) {
        const hashunit *pslot1 = buck + s1 * htl.prevhashunits;
        if (!addslot(&cd, s1, getxhash0(&htl, pslot1))) // assume WK odd
          continue;
        for (; nextcollision(&cd); ) {
          const u32 s0 = slot(&cd);
          if (htlayout_equal(&htl, buck + s0 * htl.prevhashunits, pslot1))
            candidate(eq, tree_from_bid(bucketid, s0, s1));
        }
      }
    }
  }

  size_t equi_nsols(const equi *eq) {
    return eq->nsols;
  }
  proof *equi_sols(const equi *eq) {
    return eq->sols;
  }

typedef struct {
  u32 id;
  equi *eq;
} thread_ctx;

void *worker(void *vp) {
  thread_ctx *tp = (thread_ctx *)vp;
  equi *eq = tp->eq;

//  if (tp->id == 0)
//    printf("Digit 0\n");
  if (tp->id == 0) {
    equi_clearslots(eq);
  }
  equi_digit0(eq, tp->id);
  if (tp->id == 0) {
    equi_clearslots(eq);
#ifdef EQUIHASH_SHOW_BUCKET_SIZES
    showbsizes(eq, 0);
#endif
  }
  for (u32 r = 1; r < WK; r++) {
//    if (tp->id == 0)
//      printf("Digit %d", r);
    r&1 ? equi_digitodd(eq, r, tp->id) : equi_digiteven(eq, r, tp->id);
    if (tp->id == 0) {
//      printf(" x%d b%d h%d\n", eq->xfull, eq->bfull, eq->hfull);
      equi_clearslots(eq);
#ifdef EQUIHASH_SHOW_BUCKET_SIZES
      showbsizes(eq, r);
#endif
    }
  }
//  if (tp->id == 0)
//    printf("Digit %d\n", WK);
  equi_digitK(eq, tp->id);
  return 0;
}

#endif // ZCASH_POW_TROMP_EQUI_MINER_H
