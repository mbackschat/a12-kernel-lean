use a12_kernel_rust_spike::evaluate_request_json;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::env;
use std::fs;
use std::io::{self, Write};
use std::path::Path;

const PROTOCOL_VERSION: u64 = 1;
const KERNEL_BEHAVIOR_VERSION: &str = "30.8.1";
const GROUP: &str = "Order";
const SUITE_PATH: &str = "handover/reference/flat-validation-empty-logic-v1.conformance.json";
const SUITE_ID: &str = "flat-validation-empty-logic-v1";
const OPERATION: &str = "flatValidation.evaluateFull";
const CASE_IDS: [&str; 8] = [
    "number-empty-equals-zero-content",
    "number-empty-equals-zero-empty-row",
    "boolean-empty-equals-true",
    "confirm-empty-not-true",
    "malformed-number-equals-zero",
    "healthy-or-malformed",
    "healthy-and-malformed",
    "number-not-filled-empty-row",
];

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ConformanceSuite {
    suite_id: String,
    protocol_version: u64,
    operation: String,
    kernel_behavior_version: String,
    cases: Vec<ConformanceCase>,
}

#[derive(Deserialize)]
struct ConformanceCase {
    id: String,
    request: String,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
enum Polarity {
    Value,
    Omission,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "tag", rename_all = "camelCase", deny_unknown_fields)]
enum Verdict {
    NotFired,
    Fired { polarity: Polarity },
    Unknown,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct CaseResult {
    case_id: String,
    verdict: Verdict,
}

#[derive(Serialize)]
struct AlgebraResult {
    connective: &'static str,
    left: Verdict,
    right: Verdict,
    verdict: Verdict,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Observation {
    observation_schema_version: u64,
    exercise: u8,
    case_results: Vec<CaseResult>,
    algebra_results: Vec<AlgebraResult>,
}

#[derive(Clone, Copy)]
enum VerdictInput {
    NotFired,
    FiredValue,
    FiredOmission,
    Unknown,
}

const VERDICT_INPUTS: [VerdictInput; 4] = [
    VerdictInput::NotFired,
    VerdictInput::FiredValue,
    VerdictInput::FiredOmission,
    VerdictInput::Unknown,
];

struct Branch {
    field: Value,
    condition: Value,
    cell: Option<Value>,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("flat-validation-observer: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let exercise = parse_exercise()?;
    let observation = Observation {
        observation_schema_version: 1,
        exercise,
        case_results: observe_cases()?,
        algebra_results: if matches!(exercise, 0 | 5 | 6) {
            observe_algebra()?
        } else {
            Vec::new()
        },
    };

    let stdout = io::stdout();
    let mut output = stdout.lock();
    serde_json::to_writer(&mut output, &observation)
        .map_err(|error| format!("cannot encode observation: {error}"))?;
    output
        .write_all(b"\n")
        .map_err(|error| format!("cannot write observation: {error}"))?;
    output
        .flush()
        .map_err(|error| format!("cannot flush observation: {error}"))
}

fn parse_exercise() -> Result<u8, String> {
    let arguments: Vec<_> = env::args_os().skip(1).collect();
    if arguments.len() != 2 || arguments[0] != "--exercise" {
        return Err("usage: flat-validation-observer --exercise N (N must be 0..7)".into());
    }
    let value = arguments[1]
        .to_str()
        .ok_or_else(|| "exercise must be valid UTF-8".to_string())?;
    let exercise = value
        .parse::<u8>()
        .map_err(|_| "exercise must be an integer from 0 through 7".to_string())?;
    if exercise > 7 {
        return Err("exercise must be an integer from 0 through 7".into());
    }
    Ok(exercise)
}

fn number_field(id: u64, name: &str) -> Value {
    json!({
        "id": id,
        "groupPath": [GROUP],
        "name": name,
        "kind": { "tag": "number", "scale": 2, "signed": false },
        "repeatableScope": []
    })
}

fn boolean_field(id: u64, name: &str) -> Value {
    json!({
        "id": id,
        "groupPath": [GROUP],
        "name": name,
        "kind": { "tag": "boolean" },
        "repeatableScope": []
    })
}

fn field_path(name: &str) -> Value {
    json!({ "base": "absolute", "groups": [GROUP], "field": name })
}

fn number_equals_zero(name: &str) -> Value {
    json!({
        "tag": "compare",
        "operator": "equal",
        "field": field_path(name),
        "literal": { "tag": "number", "value": "0" }
    })
}

fn boolean_equals_true(name: &str) -> Value {
    json!({
        "tag": "compare",
        "operator": "equal",
        "field": field_path(name),
        "literal": { "tag": "boolean", "value": true }
    })
}

fn parsed_boolean_cell(field_id: u64) -> Value {
    json!({
        "fieldId": field_id,
        "state": { "tag": "parsedBoolean", "value": true }
    })
}

fn malformed_cell(field_id: u64) -> Value {
    json!({
        "fieldId": field_id,
        "state": { "tag": "rejected", "cause": "malformed" }
    })
}

fn request(fields: Vec<Value>, condition: Value, cells: Vec<Value>, has_content: bool) -> Value {
    json!({
        "protocolVersion": PROTOCOL_VERSION,
        "operation": OPERATION,
        "model": {
            "fieldRefByShortNameAllowed": true,
            "repeatableGroups": [],
            "fields": fields
        },
        "declaringGroup": [GROUP],
        "condition": condition,
        "cells": cells,
        "hasContent": has_content,
        "kernelBehaviorVersion": KERNEL_BEHAVIOR_VERSION
    })
}

fn observe_cases() -> Result<Vec<CaseResult>, String> {
    let suite_text = fs::read_to_string(SUITE_PATH)
        .map_err(|error| format!("cannot read canonical suite {SUITE_PATH}: {error}"))?;
    let suite: ConformanceSuite = serde_json::from_str(&suite_text)
        .map_err(|error| format!("cannot decode canonical suite {SUITE_PATH}: {error}"))?;
    validate_suite(&suite)?;

    suite
        .cases
        .into_iter()
        .map(|case| {
            let expected_request = format!(
                "examples/reference-cli/flat-evidence/{}.request.json",
                case.id
            );
            if case.request != expected_request {
                return Err(format!(
                    "canonical case {} names unexpected request fixture {}",
                    case.id, case.request
                ));
            }
            let path = Path::new("handover").join(&case.request);
            let semantic_request = fs::read_to_string(&path).map_err(|error| {
                format!(
                    "canonical case {} cannot read request fixture {}: {error}",
                    case.id,
                    path.display()
                )
            })?;
            Ok(CaseResult {
                verdict: evaluate(&semantic_request, &case.id)?,
                case_id: case.id,
            })
        })
        .collect()
}

fn validate_suite(suite: &ConformanceSuite) -> Result<(), String> {
    if suite.suite_id != SUITE_ID
        || suite.protocol_version != PROTOCOL_VERSION
        || suite.operation != OPERATION
        || suite.kernel_behavior_version != KERNEL_BEHAVIOR_VERSION
    {
        return Err("canonical suite compatibility identity does not match the observer".into());
    }
    let actual_ids: Vec<_> = suite.cases.iter().map(|case| case.id.as_str()).collect();
    if actual_ids != CASE_IDS {
        return Err(format!(
            "canonical suite cases are missing, additional, or reordered: {actual_ids:?}"
        ));
    }
    Ok(())
}

fn verdict(input: VerdictInput) -> Verdict {
    match input {
        VerdictInput::NotFired => Verdict::NotFired,
        VerdictInput::FiredValue => Verdict::Fired {
            polarity: Polarity::Value,
        },
        VerdictInput::FiredOmission => Verdict::Fired {
            polarity: Polarity::Omission,
        },
        VerdictInput::Unknown => Verdict::Unknown,
    }
}

fn branch(input: VerdictInput, field_id: u64, field_name: &str) -> Branch {
    match input {
        VerdictInput::NotFired => Branch {
            field: boolean_field(field_id, field_name),
            condition: boolean_equals_true(field_name),
            cell: None,
        },
        VerdictInput::FiredValue => Branch {
            field: boolean_field(field_id, field_name),
            condition: boolean_equals_true(field_name),
            cell: Some(parsed_boolean_cell(field_id)),
        },
        VerdictInput::FiredOmission => Branch {
            field: number_field(field_id, field_name),
            condition: number_equals_zero(field_name),
            cell: None,
        },
        VerdictInput::Unknown => Branch {
            field: number_field(field_id, field_name),
            condition: number_equals_zero(field_name),
            cell: Some(malformed_cell(field_id)),
        },
    }
}

fn algebra_request(connective: &'static str, left: VerdictInput, right: VerdictInput) -> Value {
    let left = branch(left, 10, "LeftOperand");
    let right = branch(right, 11, "RightOperand");
    let cells = [left.cell, right.cell].into_iter().flatten().collect();
    request(
        vec![left.field, right.field],
        json!({
            "tag": connective,
            "left": left.condition,
            "right": right.condition
        }),
        cells,
        true,
    )
}

fn observe_algebra() -> Result<Vec<AlgebraResult>, String> {
    let mut results = Vec::with_capacity(32);
    for connective in ["and", "or"] {
        for left in VERDICT_INPUTS {
            for right in VERDICT_INPUTS {
                let context = format!("algebra {connective} observation");
                results.push(AlgebraResult {
                    connective,
                    left: verdict(left),
                    right: verdict(right),
                    verdict: evaluate_value(&algebra_request(connective, left, right), &context)?,
                });
            }
        }
    }
    Ok(results)
}

fn evaluate_value(semantic_request: &Value, context: &str) -> Result<Verdict, String> {
    let input = serde_json::to_string(semantic_request)
        .map_err(|error| format!("{context}: cannot encode semantic request: {error}"))?;
    evaluate(&input, context)
}

fn evaluate(input: &str, context: &str) -> Result<Verdict, String> {
    let response = serde_json::to_value(evaluate_request_json(input))
        .map_err(|error| format!("{context}: cannot encode evaluator response: {error}"))?;

    if response.get("protocolVersion").and_then(Value::as_u64) != Some(PROTOCOL_VERSION) {
        return Err(format!(
            "{context}: evaluator returned the wrong protocol version"
        ));
    }
    if response
        .get("kernelBehaviorVersion")
        .and_then(Value::as_str)
        != Some(KERNEL_BEHAVIOR_VERSION)
    {
        return Err(format!(
            "{context}: evaluator returned the wrong kernel behavior version"
        ));
    }
    match response.get("outcome").and_then(Value::as_str) {
        Some("ok") => {}
        Some("error") => {
            return Err(format!(
                "{context}: semantic request was rejected: {response}"
            ));
        }
        _ => return Err(format!("{context}: evaluator returned an invalid outcome")),
    }

    let encoded_verdict = response
        .get("verdict")
        .cloned()
        .ok_or_else(|| format!("{context}: evaluator response has no verdict"))?;
    serde_json::from_value(encoded_verdict)
        .map_err(|error| format!("{context}: evaluator returned an invalid verdict: {error}"))
}
