import os
import base64
from openai import AzureOpenAI
from azure.identity import DefaultAzureCredential, get_bearer_token_provider

endpoint = os.getenv("ENDPOINT_URL", "https://ai4mtest1.openai.azure.com/")
deployment = os.getenv("DEPLOYMENT_NAME", "gpt-5")

# Initialize Azure OpenAI client with Entra ID authentication
credential = DefaultAzureCredential(managed_identity_client_id="7e0d39de-9cb1-4585-85af-1e82ea00b36d")
token_provider = get_bearer_token_provider(credential, "https://cognitiveservices.azure.com/.default")

client = AzureOpenAI(
    azure_endpoint=endpoint,
    azure_ad_token_provider=token_provider,
    api_version="2025-01-01-preview",
)


# IMAGE_PATH = "YOUR_IMAGE_PATH"
# encoded_image = base64.b64encode(open(IMAGE_PATH, 'rb').read()).decode('ascii')
messages=[
        {
            "role": "system",
            "content": "You are a helpful assistant.",
        },
        {
            "role": "user",
            "content": "Which model is you are?",
        }
    ]

# Include speech result if speech is enabled
completion = client.chat.completions.create(
    model=deployment,
    messages=messages,
    max_completion_tokens=1600,
    stop=None,
    stream=False
)

print(completion.choices[0].message.content)
