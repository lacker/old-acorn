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

interface SearchResult {
  code: Array<string> | null;
}

interface SearchResponse {
  uri: string;
  version: number;
  error: string | null;
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

interface ClauseInfo {
  text: string;
  id: number | null;
}

interface InfoResponse {
  clause: ClauseInfo;
  premises: Array<ClauseInfo>;
  consequences: Array<ClauseInfo>;
  rule: string;
}
