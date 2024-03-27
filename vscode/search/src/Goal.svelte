<script lang="ts">
  export let searchResponse: SearchResponse;
  export let showLocation: (uri: string, range: Range) => void;

  const range = searchResponse.goalRange;
</script>

{#if searchResponse.goalName === null}
  <h1><pre>There is no goal.</pre></h1>
{:else if range === null}
  <h1><pre>{searchResponse.goalName}</pre></h1>
{:else}
  <h1>
    <pre><span
        class="goal-link"
        on:click={() => showLocation(searchResponse.uri, range)}
        >{searchResponse.goalName}</span
      ></pre>
  </h1>
{/if}

<style>
  .goal-link {
    cursor: pointer;
  }

  .goal-link:hover {
    text-decoration: underline;
  }
</style>
