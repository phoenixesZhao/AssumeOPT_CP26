#include "WeightedRandomSampling.h"

namespace rs {

void WeightedRandomSampling(size_t sampleSize,
                            const std::vector<Lit>& input, std::vector<double>& weight, std::vector<Lit>& output)
{
    // spacial cases
    if (sampleSize == 0) {
        return;
    } else if (sampleSize >= input.size()) {
        output = input;
        return;
    }

    // assign the random score u^(2^(-w)) to every element in the population
    size_t index = 0, minIndex = 0;
    double minScore = 1e30;
    for (; index < input.size(); ++index) {
        // normalized form equal to u^(2^(-w))
        double r = double((int)rand() % RAND_MAX + 1) / RAND_MAX;
        weight[index] = log(-log(r)) - weight[index];

        if (weight[index] < minScore) {
            minIndex = index;
            minScore = weight[index];
        }
    }

    // return the lit with max random score
    output.resize(sampleSize);
    if (sampleSize == 1) {
        output[0] = input[minIndex];
        return;
    }

    // sample with a reservoir
    index = 0;
    PairHeap<Lit, double> reservoir(sampleSize);
    while (reservoir.GetSize() < sampleSize) {
        reservoir.Insert(input[index], weight[index]);
        ++index;
    }
    auto& maxElement = reservoir.GetMax();
    while (index < input.size()) {
        if (weight[index] < maxElement.second) {
            reservoir.Insert(input[index], weight[index]);
            reservoir.RemoveMax();
            maxElement = reservoir.GetMax();
        }
        ++index;
    }
    reservoir.GetKeys(output);
}

}