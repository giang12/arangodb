////////////////////////////////////////////////////////////////////////////////
/// DISCLAIMER
///
/// Copyright 2018 ArangoDB GmbH, Cologne, Germany
///
/// Licensed under the Apache License, Version 2.0 (the "License");
/// you may not use this file except in compliance with the License.
/// You may obtain a copy of the License at
///
///     http://www.apache.org/licenses/LICENSE-2.0
///
/// Unless required by applicable law or agreed to in writing, software
/// distributed under the License is distributed on an "AS IS" BASIS,
/// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
/// See the License for the specific language governing permissions and
/// limitations under the License.
///
/// Copyright holder is ArangoDB GmbH, Cologne, Germany
///
/// @author Jan Christoph Uhde
////////////////////////////////////////////////////////////////////////////////

#include <boost/optional.hpp>
#include "Aql/AqlValue.h"
#include "Aql/Collection.h"
#include "Aql/OutputAqlItemRow.h"
#include "Basics/Common.h"
#include "ModificationExecutorTraits.h"
#include "VocBase/LogicalCollection.h"

#include <algorithm>

using namespace arangodb;
using namespace arangodb::aql;

ModificationExecutorBase::ModificationExecutorBase(Fetcher& fetcher, Infos& infos)
    : _infos(infos), _fetcher(fetcher), _prepared(false){};


// /// @brief skips over the taken rows if the input value is no
// /// array or empty. updates dstRow in this case and returns true!
// bool ModificationExecutorBase::skipEmptyValues(VPackSlice const& values,
//                                                size_t n, AqlItemBlock const* src,
//                                                AqlItemBlock* dst, size_t& dstRow) {
//   // TRI_ASSERT(src != nullptr);
//   // TRI_ASSERT(_operations.size() == n);
//
//   // if (values.isArray() && values.length() > 0) {
//   //  return false;
//   //}
//
//   // if (dst == nullptr) {
//   //  // fast-track exit. we don't have any output to write, so we
//   //  // better try not to copy any of the register values from src to dst
//   //  return true;
//   //}
//
//   // for (size_t i = 0; i < n; ++i) {
//   //  if (_operations[i] != IGNORE_SKIP) {
//   //    inheritRegisters(src, dst, i, dstRow);
//   //    ++dstRow;
//   //  }
//   //}
//
//   return true;
// }

template <typename Modifier>
ModificationExecutor<Modifier>::ModificationExecutor(Fetcher& fetcher, Infos& infos)
    : ModificationExecutorBase(fetcher, infos), _modifier(){};

template <typename Modifier>
ModificationExecutor<Modifier>::~ModificationExecutor() = default;

template <typename Modifier>
std::pair<ExecutionState, typename ModificationExecutor<Modifier>::Stats>
ModificationExecutor<Modifier>::produceRow(OutputAqlItemRow& output) {
  ExecutionState state = ExecutionState::HASMORE;
  ModificationExecutor::Stats stats;

  while (!_prepared && _fetcher.upstreamState() != ExecutionState::DONE) {
    std::shared_ptr<AqlItemBlockShell> block;
    std::tie(state, block) = _fetcher.fetchBlock();
    _modifier._block = block;

    if (state == ExecutionState::WAITING) {
      TRI_ASSERT(!_modifier._block);
      return {state, std::move(stats)};
    }

    if (!_modifier._block) {
      TRI_ASSERT(state == ExecutionState::DONE);
      return {state, std::move(stats)};
    }

    TRI_IF_FAILURE("ModificationBlock::getSome") {
      THROW_ARANGO_EXCEPTION(TRI_ERROR_DEBUG);
    }

    TRI_ASSERT(_modifier._block);
    TRI_ASSERT(_modifier._block->hasBlock());

    // prepares modifier for single row output
    _prepared = _modifier.doModifications(_infos, stats);

    if (!_infos._producesResults) {
      _prepared = false;
    }
  }

  // LOG_DEVEL << "prepared: " << _prepared;

  if (_prepared) {
    TRI_ASSERT(_modifier._block);
    TRI_ASSERT(_modifier._block->hasBlock());

    // LOG_DEVEL << "call doOutput";
    bool thisBlockHasMore = _modifier.doOutput(this->_infos, output);

    if (thisBlockHasMore) {
      // LOG_DEVEL << "doOutput OPRES HASMORE";
      return {ExecutionState::HASMORE, std::move(stats)};
    } else {
      // LOG_DEVEL << "doOutput NEED NEW BLOCK";
      // we need to get a new block
      _prepared = false;
    }
  }

  // LOG_DEVEL << "exit produceRow";
  return {_fetcher.upstreamState(), std::move(stats)};
}

template class ::arangodb::aql::ModificationExecutor<Insert>;
template class ::arangodb::aql::ModificationExecutor<Remove>;
template class ::arangodb::aql::ModificationExecutor<Replace>;
template class ::arangodb::aql::ModificationExecutor<Update>;
template class ::arangodb::aql::ModificationExecutor<Upsert>;
