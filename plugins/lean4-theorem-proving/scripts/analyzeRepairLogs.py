#!/usr/bin/env python3
"""
Analyze repair attempt logs to discover successful patterns and optimize strategies.

Reads NDJSON logs from .repair/attempts.ndjson and generates insights:
- Success rates by error type
- Effective repair strategies
- Stage escalation patterns
- Cost optimization opportunities

Inspired by APOLLO's learning from compiler feedback
https://arxiv.org/abs/2505.05758
"""

import json
import sys
from pathlib import Path
from collections import defaultdict, Counter
from typing import List, Dict, Any


def load_attempts(log_file: Path) -> List[Dict[str, Any]]:
    """Load attempts from NDJSON file."""
    attempts = []
    with open(log_file) as f:
        for line in f:
            line = line.strip()
            if line:
                attempts.append(json.loads(line))
    return attempts


def analyze_success_by_error_type(attempts: List[Dict]) -> Dict[str, Dict]:
    """Analyze success rates by error type."""
    by_error = defaultdict(lambda: {"total": 0, "success": 0, "attempts": []})

    for attempt in attempts:
        if "error" in attempt:
            error_type = attempt.get("errorType", "unknown")
            by_error[error_type]["total"] += 1
            if attempt.get("success"):
                by_error[error_type]["success"] += 1
            by_error[error_type]["attempts"].append(attempt)

    # Calculate success rates
    results = {}
    for error_type, data in by_error.items():
        total = data["total"]
        success = data["success"]
        rate = (success / total * 100) if total > 0 else 0
        results[error_type] = {
            "total": total,
            "success": success,
            "rate": rate,
            "attempts": data["attempts"]
        }

    return results


def analyze_solver_effectiveness(attempts: List[Dict]) -> Dict[str, int]:
    """Analyze how often solver cascade succeeds."""
    solver_success = 0
    agent_success = 0
    total = 0

    for attempt in attempts:
        if attempt.get("success"):
            total += 1
            if attempt.get("solverSuccess"):
                solver_success += 1
            elif attempt.get("agentCalled"):
                agent_success += 1

    return {
        "solver_success": solver_success,
        "agent_success": agent_success,
        "total_success": total,
        "solver_rate": (solver_success / total * 100) if total > 0 else 0
    }


def analyze_stage_usage(attempts: List[Dict]) -> Dict[str, int]:
    """Analyze Stage 1 vs Stage 2 usage."""
    stage_counter = Counter()
    stage_success = defaultdict(int)

    for attempt in attempts:
        stage = attempt.get("stage", 1)
        stage_counter[stage] += 1
        if attempt.get("success"):
            stage_success[stage] += 1

    return {
        "stage1_attempts": stage_counter.get(1, 0),
        "stage2_attempts": stage_counter.get(2, 0),
        "stage1_success": stage_success.get(1, 0),
        "stage2_success": stage_success.get(2, 0)
    }


def estimate_cost(attempts: List[Dict]) -> Dict[str, float]:
    """Estimate cost based on stage usage."""
    # Rough estimates per attempt
    SOLVER_COST = 0.0  # Free
    STAGE1_COST = 0.001  # Haiku
    STAGE2_COST = 0.01  # Sonnet

    total_cost = 0.0
    solver_cost = 0.0
    stage1_cost = 0.0
    stage2_cost = 0.0

    for attempt in attempts:
        if attempt.get("solverSuccess"):
            solver_cost += SOLVER_COST
        elif attempt.get("agentCalled"):
            stage = attempt.get("stage", 1)
            if stage == 1:
                stage1_cost += STAGE1_COST
            else:
                stage2_cost += STAGE2_COST

    total_cost = solver_cost + stage1_cost + stage2_cost

    return {
        "total": total_cost,
        "solver": solver_cost,
        "stage1": stage1_cost,
        "stage2": stage2_cost
    }


def identify_patterns(attempts: List[Dict]) -> List[str]:
    """Identify interesting patterns in attempts."""
    patterns = []

    # Pattern 1: Repeated errors
    error_sequences = defaultdict(list)
    for attempt in attempts:
        error_hash = attempt.get("errorHash", "")
        if error_hash:
            error_sequences[error_hash].append(attempt)

    for error_hash, sequence in error_sequences.items():
        if len(sequence) >= 3:
            patterns.append(
                f"⚠️  Error {error_hash[:8]} repeated {len(sequence)} times "
                f"(may need different approach)"
            )

    # Pattern 2: Quick successes
    quick_successes = [a for a in attempts if a.get("success") and a.get("elapsed", 999) < 5]
    if quick_successes:
        patterns.append(
            f"✓ {len(quick_successes)} quick successes (<5s) - "
            f"solver cascade or simple fixes"
        )

    # Pattern 3: Stage 2 escalations
    stage2_attempts = [a for a in attempts if a.get("stage") == 2]
    if stage2_attempts:
        stage2_success = sum(1 for a in stage2_attempts if a.get("success"))
        rate = (stage2_success / len(stage2_attempts) * 100) if stage2_attempts else 0
        patterns.append(
            f"🔼 Stage 2 used {len(stage2_attempts)} times, "
            f"success rate: {rate:.1f}%"
        )

    return patterns


def generate_report(log_file: Path) -> str:
    """Generate comprehensive analysis report."""
    attempts = load_attempts(log_file)

    if not attempts:
        return "No attempts found in log file."

    # Analyze different aspects
    by_error = analyze_success_by_error_type(attempts)
    solver_stats = analyze_solver_effectiveness(attempts)
    stage_stats = analyze_stage_usage(attempts)
    costs = estimate_cost(attempts)
    patterns = identify_patterns(attempts)

    # Generate report
    report = []
    report.append("=" * 60)
    report.append("Repair Attempt Log Analysis")
    report.append("=" * 60)
    report.append("")

    # Overall stats
    total_attempts = len(attempts)
    successful = sum(1 for a in attempts if a.get("success"))
    success_rate = (successful / total_attempts * 100) if total_attempts > 0 else 0

    report.append("📊 Overall Statistics")
    report.append("-" * 60)
    report.append(f"Total attempts: {total_attempts}")
    report.append(f"Successful: {successful}")
    report.append(f"Success rate: {success_rate:.1f}%")
    report.append("")

    # Success by error type
    if by_error:
        report.append("📈 Success Rates by Error Type")
        report.append("-" * 60)
        for error_type, stats in sorted(by_error.items(), key=lambda x: x[1]['rate'], reverse=True):
            report.append(
                f"{error_type:20s}: {stats['success']:3d}/{stats['total']:3d} "
                f"({stats['rate']:5.1f}%)"
            )
        report.append("")

    # Solver effectiveness
    report.append("🤖 Solver Cascade vs Agent")
    report.append("-" * 60)
    report.append(f"Solver cascade success: {solver_stats['solver_success']} "
                  f"({solver_stats['solver_rate']:.1f}%)")
    report.append(f"Agent repair success: {solver_stats['agent_success']}")
    report.append("")

    # Stage usage
    report.append("🎯 Stage Usage")
    report.append("-" * 60)
    stage1_rate = (stage_stats['stage1_success'] / stage_stats['stage1_attempts'] * 100) \
        if stage_stats['stage1_attempts'] > 0 else 0
    stage2_rate = (stage_stats['stage2_success'] / stage_stats['stage2_attempts'] * 100) \
        if stage_stats['stage2_attempts'] > 0 else 0

    report.append(f"Stage 1 (Haiku): {stage_stats['stage1_attempts']} attempts, "
                  f"{stage_stats['stage1_success']} success ({stage1_rate:.1f}%)")
    report.append(f"Stage 2 (Sonnet): {stage_stats['stage2_attempts']} attempts, "
                  f"{stage_stats['stage2_success']} success ({stage2_rate:.1f}%)")
    report.append("")

    # Cost estimate
    report.append("💰 Estimated Cost")
    report.append("-" * 60)
    report.append(f"Total: ${costs['total']:.2f}")
    report.append(f"  Solver cascade: ${costs['solver']:.2f} (free)")
    report.append(f"  Stage 1 (Haiku): ${costs['stage1']:.2f}")
    report.append(f"  Stage 2 (Sonnet): ${costs['stage2']:.2f}")
    report.append("")

    # Patterns
    if patterns:
        report.append("🔍 Patterns Detected")
        report.append("-" * 60)
        for pattern in patterns:
            report.append(f"  {pattern}")
        report.append("")

    # Recommendations
    report.append("💡 Recommendations")
    report.append("-" * 60)

    if solver_stats['solver_rate'] < 30:
        report.append("  ⚠️  Low solver cascade success rate - review error types")

    if stage_stats['stage2_attempts'] > stage_stats['stage1_attempts']:
        report.append("  ⚠️  Heavy Stage 2 usage - check if Stage 1 needs tuning")

    if success_rate < 50:
        report.append("  ⚠️  Low overall success rate - may need manual intervention")
    elif success_rate > 80:
        report.append("  ✓ Excellent success rate!")

    report.append("")
    report.append("=" * 60)

    return "\n".join(report)


def main():
    if len(sys.argv) < 2:
        print("Usage: analyzeRepairLogs.py ATTEMPTS.ndjson", file=sys.stderr)
        print("\nAnalyzes repair attempt logs to discover patterns.", file=sys.stderr)
        print("\nExample:", file=sys.stderr)
        print("  python3 analyzeRepairLogs.py .repair/attempts.ndjson", file=sys.stderr)
        sys.exit(1)

    log_file = Path(sys.argv[1])
    if not log_file.exists():
        print(f"Error: Log file not found: {log_file}", file=sys.stderr)
        sys.exit(1)

    report = generate_report(log_file)
    print(report)


if __name__ == "__main__":
    main()
