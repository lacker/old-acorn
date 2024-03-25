// Interfaces with the language server.
// This should be kept parallel to interfaces.rs.

interface ProgressResponse {
  done: number;
  total: number;
}

interface SearchParams {
  uri: string;
  version: number;
  selectedLine: number;
  id: number;
}

interface AssumptionInfo {
  uri: string;
  range: any;
  theoremName: string | null;
  negatedGoal: boolean;
}

interface ClauseInfo {
  text: string;
  id: number | null;
}

interface ProofStepInfo {
  clause: ClauseInfo;
  premises: Array<[String, ClauseInfo]>;
  rule: string;
}

interface SearchResult {
  code: Array<string> | null;
  steps: Array<ProofStepInfo> | null;
}

interface SearchResponse {
  uri: string;
  version: number;
  failure: string | null;
  loading: boolean;
  goalName: string | null;
  textOutput: Array<string>;
  proofInsertionLine: number;
  result: SearchResult | null;
  id: number;
}

interface InfoParams {
  searchId: number;
  clauseId: number;
}

interface InfoResult {
  clause: ClauseInfo;
  step: ProofStepInfo;
  consequences: Array<ProofStepInfo>;
}

interface InfoResponse {
  searchId: number;
  failure: string | null;
  result: InfoResult | null;
}
