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

interface Position {
  line: number;
  character: number;
}

interface Range {
  start: Position;
  end: Position;
}

interface Location {
  uri: string;
  range: Range;
}

interface ClauseInfo {
  text: string | null;
  id: number | null;
}

interface ProofStepInfo {
  clause: ClauseInfo;
  premises: Array<[String, ClauseInfo]>;
  rule: string;
  location: Location | null;
  depth: number;
}

interface SearchStatus {
  code: Array<string> | null;
  codeError: string | null;
  steps: Array<ProofStepInfo> | null;
  outcome: string | null;
  needsSimplification: boolean | null;
  numActivated: number;
}

interface SearchResponse {
  uri: string;
  version: number;
  failure: string | null;
  loading: boolean;
  goalName: string | null;
  goalRange: Range | null;
  proofInsertionLine: number;
  insertBlock: boolean;
  status: SearchStatus;
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
  numConsequences: number;
}

interface InfoResponse {
  searchId: number;
  failure: string | null;
  result: InfoResult | null;
}
