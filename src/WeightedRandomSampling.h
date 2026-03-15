#pragma once
#include <vector>
#include "typedefs.hpp"

namespace rs {

void WeightedRandomSampling(size_t sampleSize,
                            const std::vector<Lit>& input, std::vector<double>& weight, std::vector<Lit>& output);

template <typename Key, typename Score>
struct PairHeap
{
    std::vector<std::pair<Key, Score>> tree_;

    explicit PairHeap(size_t size);
    void Reserve(size_t size);

    bool IsEmpty();
    size_t GetSize();
    std::pair<Key, Score>& GetMax();
    void GetKeys(std::vector<Key>& out);

    void Insert(Key k, Score s);
    void RemoveMax();
};

template <typename Key, typename Score>
PairHeap<Key, Score>::PairHeap(size_t size)
{
    tree_.emplace_back();
    tree_.reserve(size + 10);
}

template <typename Key, typename Score>
void PairHeap<Key, Score>::Reserve(size_t size)
{
    tree_.reserve(size + 10);
}

template <typename Key, typename Score>
bool PairHeap<Key, Score>::IsEmpty()
{
    return tree_.size() <= 1;
}

template <typename Key, typename Score>
size_t PairHeap<Key, Score>::GetSize()
{
    return tree_.size() - 1;
}

template <typename Key, typename Score>
void PairHeap<Key, Score>::GetKeys(std::vector<Key> &out)
{
    if (GetSize() <= 1) {
        return;
    }
    out.resize(GetSize());
    for (size_t i = 1; i < tree_.size(); ++i) {
        out[i - 1] = tree_[i].first;
    }
}

template <typename Key, typename Score>
std::pair<Key, Score>& PairHeap<Key, Score>::GetMax()
{
    if (IsEmpty()) {
        return tree_[0];
    } else {
        return tree_[1];
    }
}

template <typename Key, typename Score>
void PairHeap<Key, Score>::Insert(Key k, Score s)
{
    size_t pos = tree_.size();
    tree_.emplace_back(k, s);
    while (pos > 1 && tree_[pos >> 1].second < s) {
        std::swap(tree_[pos], tree_[pos >> 1]);
        pos >>= 1;
    }
}

template <typename Key, typename Score>
void PairHeap<Key, Score>::RemoveMax()
{
    if (IsEmpty()) {
        return;
    }

    size_t pos = 1;
    std::swap(tree_[1], tree_[tree_.size() - 1]);
    tree_.pop_back();
    while ((pos << 1) < tree_.size()) {
        // pos is not a leaf
        size_t leftPos = (pos << 1), rightPos = (pos << 1 | 1);

        // leftPos is the last element
        if (rightPos == tree_.size()) {
            if (tree_[leftPos].second > tree_[pos].second) {
                std::swap(tree_[leftPos], tree_[pos]);
            }
            return;
        }

        // both leftPos and rightPos exist
        if (tree_[leftPos].second <= tree_[pos].second && tree_[rightPos].second <= tree_[pos].second) {
            break;
        } else if (tree_[leftPos].second > tree_[rightPos].second) {
            std::swap(tree_[pos], tree_[leftPos]);
            pos = leftPos;
        } else {
            std::swap(tree_[pos], tree_[rightPos]);
            pos = rightPos;
        }
    }
}

}
