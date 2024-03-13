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
