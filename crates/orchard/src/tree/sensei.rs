use super::*;
#[allow(unused_imports)]
use crate::backend::prelude::*;
pub(super) fn merkle_crh(
    level: Level,
    left: &MerkleHashOrchard,
    right: &MerkleHashOrchard,
) -> pallas::Base {
    #[cfg(feature = "weighted-merkle")]
    {
        sensei::primitives::merkle::weighted_hash(level.into(), left.0, right.0)
    }
    #[cfg(not(feature = "weighted-merkle"))]
    {
        sensei::primitives::merkle::hash(level.into(), left.0, right.0)
    }
}
impl MerkleHashOrchard {
    /// Combines same-level node pairs in order, sharing normalization across the batch.
    pub fn combine_batch<'a>(
        level: Level,
        pairs: impl IntoIterator<Item = (&'a Self, &'a Self)>,
    ) -> Vec<Self> {
        #[cfg(feature = "weighted-merkle")]
        {
            let mut workspace = MerkleHashBatchWorkspace::default();
            let mut output = Vec::new();
            Self::combine_batch_with_workspace(level, pairs, &mut workspace, &mut output);
            output
        }

        #[cfg(not(feature = "weighted-merkle"))]
        {
            sensei::primitives::merkle::hash_batch(
                level.into(),
                pairs.into_iter().map(|(l, r)| (l.0, r.0)),
            )
            .into_iter()
            .map(MerkleHashOrchard)
            .collect()
        }
    }
    #[cfg(feature = "weighted-merkle")]
    /// Combines node pairs while reusing temporary allocations and the output buffer.
    pub fn combine_batch_with_workspace<'a>(
        level: Level,
        pairs: impl IntoIterator<Item = (&'a Self, &'a Self)>,
        workspace: &mut MerkleHashBatchWorkspace,
        output: &mut Vec<Self>,
    ) {
        let hashes = sensei::primitives::merkle::weighted_hash_batch(
            level.into(),
            pairs.into_iter().map(|(l, r)| (l.0, r.0)),
            &mut workspace.inner,
        );
        output.clear();
        output.extend(hashes.iter().copied().map(MerkleHashOrchard));
    }
}
