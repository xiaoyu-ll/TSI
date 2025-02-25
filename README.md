# On Temporal-Constraint Subgraph Matching
# ABSTRACT
Temporal-constraint subgraph matching has emerged as a significant challenge in the study of temporal graphs, which model dynamic relationships across various domains, such as social networks and transaction networks. However, the problem of temporal-constraint subgraph matching is NP-hard. Furthermore, because each temporal-constraint contains a permutation of temporal parameters, existing subgraph matching acceleration techniques demonstrate limited applicability to temporal-constrained graphs. Traditional continuous subgraph matching approaches prove inadequate in addressing this complex problem due to their inability to effectively handle temporal constraints. This paper addresses the challenge of identifying subgraphs that not only structurally align with a given query graph but also satisfy specific temporal-constraints on the edges. We introduce three novel algorithms to tackle this issue: the TCSM-V2V algorithm, which uses a vertex-to-vertex expansion strategy and effectively prunes non-matching vertices by integrating both query and temporal-constraints into a temporal-constraint query graph; the TCSM-E2E algorithm, which employs an edge-to-edge expansion strategy, significantly reducing matching time by minimizing vertex permutation processes; and the TCSM-EVE algorithm, which combines edge-vertex-edge expansion to eliminate duplicate matches by avoiding both vertex and edge permutations. Notably, our optimal TCSM-EVE algorithm achieves an average three-order-of-magnitude speedup on large-scale datasets. Extensive experiments conducted across 6 datasets demonstrate that our approach outperforms existing methods in terms of both accuracy and computational efficiency.

# Datasets

Because some datasets used in the paper are too large to be uploaded to GitHub, you can download  them at https://pan.quark.cn/s/1308697e75fa

# Compile
All experiments are compiled in the same way, first in the ` exp3 ` directory.


` cd exp3 `


` g++ -O3 main.cpp -o main `


` g++ -O3 vtv.cpp -o vtv `


` g++ -O3 ete.cpp -o ete `


` g++ -O3 eve.cpp -o eve `


# Run
To run the program, you can choose an algorithm to run.


` ./main `



` vtv ` or ` ete ` or ` eve `
