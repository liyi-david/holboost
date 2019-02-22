Require Import Holboost.plugin.

Boom Enable OpaqueProofExtraction.

Boom Refresh.

Boom Print min_l.
Boom Remote "assert task['min_l'].body is not None, 'failed to extract from opaque proof min_l.'".
