# Lean4-Memories Integration for Compiler-Guided Repair

**Status:** Design note for future implementation

**Goal:** Enable the repair system to learn successful patterns and improve over time by integrating with the lean4-memories MCP server.

---

## Overview

The compiler-guided repair system generates structured logs (`.repair/attempts.ndjson`) containing rich information about what strategies work for which error types. By feeding this data into lean4-memories, we can:

1. **Learn successful patterns** - Which fixes work for which error types
2. **Avoid repeated failures** - Don't retry strategies that failed recently
3. **Personalize to codebase** - Adapt to project-specific patterns
4. **Improve over time** - Success rate increases as memory builds

---

## Data to Store

### Entities

**Error Pattern**
```
Entity: error_pattern_type_mismatch
Type: ErrorPattern
Observations:
- "Occurs frequently in continuity proofs (12 times)"
- "Most common in topology files (8/12 occurrences)"
- "Usually involves Measurable vs Continuous mismatch"
```

**Repair Strategy**
```
Entity: strategy_convert_with_depth_2
Type: RepairStrategy
Observations:
- "Frequently successful for type_mismatch errors"
- "Usually resolves quickly"
- "Works best when goal involves type class instances"
- "Low cost (Stage 1)"
```

**Mathlib Lemma Usage**
```
Entity: lemma_continuous_of_measurable
Type: MathlibLemma
Observations:
- "Used successfully in 15 repairs"
- "Common for: Measurable f → Continuous f conversions"
- "Import: Mathlib.Topology.Basic"
```

### Relations

```
error_pattern_type_mismatch --solvedBy--> strategy_convert_with_depth_2
strategy_convert_with_depth_2 --uses--> lemma_continuous_of_measurable
error_pattern_type_mismatch --occursIn--> file_topology_instances
```

---

## Integration Points

### 1. Post-Repair Learning

After successful repair session:

```python
# Parse attempts.ndjson
successful_repairs = [a for a in attempts if a['success']]

for repair in successful_repairs:
    # Store successful pattern
    mcp__memory__create_entities([{
        "name": f"repair_{repair['errorHash']}",
        "entityType": "SuccessfulRepair",
        "observations": [
            f"Error type: {repair['errorType']}",
            f"Strategy: {repair['strategy']}",
            f"Attempts needed: {repair['attempt']}",
            f"Stage used: {repair['stage']}",
            f"File: {repair['file']}",
            f"Mathlib lemmas: {', '.join(repair.get('lemmasUsed', []))}"
        ]
    }])

    # Create relations
    mcp__memory__create_relations([{
        "from": f"error_{repair['errorType']}",
        "to": f"repair_{repair['errorHash']}",
        "relationType": "solvedBy"
    }])
```

### 2. Pre-Repair Query

Before attempting repair:

```python
# Query similar past repairs
similar_repairs = mcp__memory__search_nodes(
    query=f"{error_type} {goal_keywords}"
)

# Extract successful strategies
successful_strategies = []
for node in similar_repairs['entities']:
    if 'Success rate' in node['observations']:
        successful_strategies.append(extract_strategy(node))

# Prioritize strategies by past success rate
strategies = sort_by_success_rate(successful_strategies)

# Try top strategies first before generic approach
for strategy in strategies[:3]:
    if try_strategy(strategy):
        return success
```

### 3. Pattern Mining

Periodically analyze memory to discover meta-patterns:

```python
# Find error types with high success rates
high_success_errors = query_memory(
    "error patterns with success rate > 80%"
)

# Find underperforming strategies
low_success_strategies = query_memory(
    "repair strategies with success rate < 30%"
)

# Identify codebase-specific patterns
project_patterns = query_memory(
    "repairs in files matching */probability/*"
)

# Generate insights
insights = generate_insights(
    high_success_errors,
    low_success_strategies,
    project_patterns
)

# Update error routing config
update_errorStrategies_yaml(insights)
```

---

## Implementation Phases

### Phase 1: Basic Storage (Low-hanging fruit)

**Implement:**
- Post-repair hook stores successful repairs
- Simple entity/relation creation
- No retrieval yet, just accumulation

**Value:** Start building history for future use

**Effort:** 1-2 hours

### Phase 2: Query Integration (Medium effort)

**Implement:**
- Pre-repair queries for similar past cases
- Strategy prioritization based on memory
- Feedback loop: successful strategies used more often

**Value:** Improved success rate through pattern learning

**Effort:** 4-6 hours

### Phase 3: Pattern Mining (High value)

**Implement:**
- analyzeRepairLogs.py reads from memory
- Automated insight generation
- Dynamic errorStrategies.yaml updates

**Value:** Continuous improvement, personalization

**Effort:** 8-12 hours

### Phase 4: Cross-Project Learning (Advanced)

**Implement:**
- Share successful patterns across projects
- Community pattern library
- Mathlib-wide strategy recommendations

**Value:** Ecosystem-wide improvement

**Effort:** Significant (requires infrastructure)

---

## Example Memory Session

**Initial state:** Empty memory

**After 10 repairs:**
```
Entities: 10 successful repairs, 5 error patterns, 15 strategies
Relations: 30 (repairs → strategies → lemmas)
```

**Query:** "How to fix type_mismatch in continuity proofs?"

**Memory returns:**
```
✓ 3 past cases found
  - repair_a3f2b1: Used convert + simp (success on attempt 2)
  - repair_d8c4e5: Used continuous_of_measurable (success on attempt 1)
  - repair_b2a9f3: Used type annotation (success on attempt 3)

Recommended approach:
1. Try continuous_of_measurable (most successful, fastest)
2. If fail, try convert + simp (frequently successful)
3. If fail, try type annotation (fallback)
```

**After 100 repairs:**
```
Entities: 100+ repairs, 10 error patterns, 50+ strategies
Relations: 200+

Success rate improves with memory guidance
Faster convergence (fewer attempts needed)
Cost reduced through learning (fewer failed attempts)
```

---

## Schema Design

```typescript
// Error pattern entity
interface ErrorPattern {
  name: string;  // e.g., "error_pattern_type_mismatch"
  entityType: "ErrorPattern";
  observations: [
    "Total occurrences: N",
    "Success rate: X%",
    "Common in: [file patterns]",
    "Typical goal keywords: [keywords]"
  ];
}

// Repair strategy entity
interface RepairStrategy {
  name: string;  // e.g., "strategy_convert_depth_2"
  entityType: "RepairStrategy";
  observations: [
    "Success rate: X%",
    "Avg attempts: N",
    "Cost per attempt: $X",
    "Works best for: [error types]",
    "Requires: [lemmas/imports]"
  ];
}

// Successful repair instance
interface SuccessfulRepair {
  name: string;  // e.g., "repair_abc123"
  entityType: "SuccessfulRepair";
  observations: [
    "Error type: type_mismatch",
    "File: path/to/file.lean:line",
    "Goal: Continuous f",
    "Strategy: convert_depth_2",
    "Lemmas used: continuous_of_measurable, simp",
    "Attempts needed: 2",
    "Stage: 1",
    "Elapsed: 3.2s",
    "Date: 2025-10-28"
  ];
}
```

---

## Metrics to Track

Track these metrics before and after memory integration to measure improvement:

**Key metrics:**
- Success rate by error type
- Average attempts to success
- Solver cascade effectiveness
- Cost per successful repair

**Expected improvements with memory integration:**
- Higher success rate through pattern learning
- Faster convergence (fewer attempts)
- Reduced cost (fewer failed attempts)
- Better strategy selection over time

**Learning curve:** Success rate should improve with each session as memory accumulates.

---

## Code Hooks

### analyzer.py modification

```python
# After analyzing attempts.ndjson
def store_in_memory(successful_repairs):
    """Store successful repairs in lean4-memories."""
    if not memory_available():
        return

    for repair in successful_repairs:
        entity = format_repair_entity(repair)
        mcp__memory__create_entities([entity])

        # Create relations to strategies
        if repair.get('strategy'):
            mcp__memory__create_relations([{
                "from": entity['name'],
                "to": f"strategy_{repair['strategy']}",
                "relationType": "usedStrategy"
            }])
```

### proposePatch.py modification

```python
# Before generating patch
def query_memory_for_similar(error_context):
    """Query memory for similar past cases."""
    if not memory_available():
        return []

    results = mcp__memory__search_nodes(
        query=f"{error_context['errorType']} {' '.join(error_context['suggestionKeywords'])}"
    )

    return extract_successful_strategies(results)
```

---

## Benefits

1. **Personalized** - Learns project-specific patterns
2. **Improving** - Success rate increases over time
3. **Cost-efficient** - Fewer failed attempts
4. **Knowledge base** - Builds searchable repair patterns
5. **Community value** - Patterns can be shared

---

## Next Steps

1. **Prototype Phase 1** - Basic storage hook
2. **Test with real repairs** - Validate schema design
3. **Implement Phase 2** - Query integration
4. **Measure improvement** - Track metrics
5. **Iterate** - Refine based on results

---

*Design note for future lean4-memories integration*
*Status: Planned for future implementation*
*Version: 1.0*
*Date: 2025-10-28*
