<script lang="ts">
  import { onMount } from "svelte";

  let content = "No message received yet";

  onMount(() => {
    window.addEventListener("message", (event) => {
      const message = event.data;
      content = JSON.stringify(message, null, 2);
    });
  });
</script>

<main>
  <h1>Message from Extension:</h1>
  <pre>{content}</pre>
</main>
