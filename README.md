# On Temporal-Constraint Subgraph Matching
# ABSTRACT
Temporal-constraint subgraph matching has emerged as a significant challenge in the study of temporal graphs, which model dynamic relationships across various domains, such as social networks and communication networks. However, the problem of temporal- constraint subgraph matching is NP-hard. Furthermore, because each temporal sequence contains a permutation of times, existing subgraph matching acceleration techniques are difficult to apply to graphs with temporal constraints. For instance, the baseline RI-DS algorithm takes 22 hours to match a query 𝑞 with a temporal constraint 𝑡𝑐 on the 8-million-scale WT dataset. This paper addresses the challenge of identifying subgraphs that not only structurally align with a given query graph but also satisfy specific temporal constraints on the edges. We introduce three novel algorithms to tackle this issue: the TCSM-V2V algorithm, which uses a vertex- to-vertex expansion strategy and effectively prunes non-matching vertices by integrating both query and temporal constraints into a temporal-constraint query graph; the TCSM-E2E algorithm, which employs an edge-to-edge expansion strategy, significantly reducing matching time by minimizing vertex permutation processes; and the TCSM-EVE algorithm, which combines edge-vertex-edge expansion to eliminate duplicate matches by avoiding both vertex and edge permutations. The best TCSM-EVE algorithm matches query 𝑞 with 𝑡𝑐 on WT in just 84 seconds, achieving a three-order- of-magnitude speedup. Extensive experiments conducted across 7 datasets demonstrate that our approach outperforms existing methods in terms of both accuracy and computational efficiency.

# Datasets

Because some datasets used in the paper are too large to be uploaded to GitHub, you can download  them at https://pan.quark.cn/s/1308697e75fa

# Compile

'''
g++ main.cpp -o main -std=c++11 -O3
'''


# Run
To run the program, run the following command.
./main
