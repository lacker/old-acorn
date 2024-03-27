<script lang="ts">
  export let step: ProofStepInfo;
  export let showLocation: (uri: string, range: Range) => void;

  const rule = step.rule.toLowerCase();
  const source = step.source;
</script>

{#if source !== null}
  <span
    class="preview-link"
    on:click={() => showLocation(source.uri, source.range)}>{rule}</span
  >
{:else}
  <span>{rule}</span>
{/if}

<style>
  .preview-link {
    cursor: pointer;
    color: var(--vscode-textLink-foreground);
  }

  .preview-link:hover {
    text-decoration: underline;
  }
</style>
